use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use egg::{Analysis, EGraph, Id};
use svg::Document;
use svg::node::Text as TextNode;
use svg::node::element::{Line, Rectangle, Text};

use crate::{SwpSolution, TileLang};

const PALETTE: &[&str] = &[
    "#e76f51", "#2a9d8f", "#f4a261", "#264653", "#e9c46a", "#8ecae6", "#bb9457", "#c77dff",
];

const CYCLE_W: i32 = 60;
const LANE_H: i32 = 36;
const LABEL_W: i32 = 70;
const PAD: i32 = 16;
const AXIS_H: i32 = 22;
const GROUP_PAD: i32 = 10;

struct Op {
    name: String,
    t: i32,
    d: i32,
    resource: usize,
}

struct Placed {
    resource: usize,
    lane: usize,
    start: i32,
    dur: i32,
    op: String,
    iter: i32,
}

fn text(x: i32, y: i32, size: i32, content: impl Into<String>) -> Text {
    Text::new("")
        .set("x", x)
        .set("y", y)
        .set("font-size", size)
        .add(TextNode::new(content.into()))
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rectangle {
    Rectangle::new()
        .set("x", x)
        .set("y", y)
        .set("width", w)
        .set("height", h)
}

fn vline(x: i32, y0: i32, y1: i32, stroke: &str) -> Line {
    Line::new()
        .set("x1", x)
        .set("y1", y0)
        .set("x2", x)
        .set("y2", y1)
        .set("stroke", stroke)
}

pub fn render_pipeline<N>(
    egraph: &EGraph<TileLang, N>,
    resource_limits: &[i32],
    sol: &SwpSolution,
    path: &str,
) -> std::io::Result<()>
where
    N: Analysis<TileLang>,
{
    let ii = sol.ii as i32;
    let l = sol.end as i32;
    let n_iters = ((l + ii - 1) / ii).max(1);

    // Dragon-book phase breakdown
    let prologue = (n_iters - 1) * ii;
    let steady = ii;
    let epilogue = (l - ii).max(0);
    let total_cycles = prologue + steady + epilogue;
    debug_assert_eq!(total_cycles, l + (n_iters - 1) * ii);

    let duration = class_durations(egraph);
    let ops = collect_ops(egraph, resource_limits.len(), sol, &duration);
    let color = assign_colors(&ops);
    let (placed, lanes_per_resource) = pack_lanes(&ops, resource_limits, ii, n_iters);

    let n_resources = resource_limits.len();
    let mut y_top: Vec<i32> = Vec::with_capacity(n_resources);
    let mut y = PAD + AXIS_H;
    for r in 0..n_resources {
        y_top.push(y);
        y += lanes_per_resource[r] * LANE_H + GROUP_PAD;
    }
    let height = y + PAD;
    let width = LABEL_W + total_cycles * CYCLE_W + PAD * 2;

    let mut doc = Document::new()
        .set("width", width)
        .set("height", height)
        .set("font-family", "monospace");

    doc = doc.add(rect(0, 0, width, height).set("fill", "white"));

    // Iteration band shading
    let band_top = PAD + AXIS_H;
    let band_h = height - PAD * 2 - AXIS_H;
    for iter in 0..n_iters {
        let x0 = PAD + LABEL_W + iter * ii * CYCLE_W;
        let fill = if iter % 2 == 0 { "#fafafa" } else { "#eef2f7" };
        doc = doc.add(rect(x0, band_top, ii * CYCLE_W, band_h).set("fill", fill));
    }

    // Cycle grid + labels
    for c in 0..=total_cycles {
        let x = PAD + LABEL_W + c * CYCLE_W;
        let stroke = if c % ii == 0 { "#aaa" } else { "#e8e8e8" };
        doc = doc.add(vline(x, PAD + AXIS_H, height - PAD, stroke));
        doc = doc.add(
            text(x, PAD + AXIS_H - 6, 10, c.to_string())
                .set("text-anchor", "middle")
                .set("fill", "#555"),
        );
    }

    // Resource labels
    for r in 0..n_resources {
        doc = doc.add(
            text(PAD, y_top[r] + LANE_H / 2 + 4, 12, format!("R{r}"))
                .set("font-weight", "bold")
                .set("fill", "#000"),
        );
    }

    // Op boxes
    for p in &placed {
        let x = PAD + LABEL_W + p.start * CYCLE_W;
        let y = y_top[p.resource] + (p.lane as i32) * LANE_H + 3;
        let w = p.dur * CYCLE_W;
        let h = LANE_H - 6;
        let fill = color.get(&p.op).copied().unwrap();
        doc = doc.add(
            rect(x, y, w, h)
                .set("fill", fill)
                .set("stroke", "#222")
                .set("stroke-width", 1),
        );
        doc = doc.add(
            text(x + w / 2, y + h / 2, 11, format!("{op}#{i}", op = p.op, i = p.iter))
                .set("fill", "white")
                .set("font-weight", "bold")
                .set("text-anchor", "middle")
                .set("dominant-baseline", "middle"),
        );
    }

    svg::save(path, &doc)?;

    let png_path = Path::new(path).with_extension("png");
    let status = Command::new("rsvg-convert")
        .args(["-z", "3", path, "-o"])
        .arg(&png_path)
        .status()?;
    if !status.success() {
        return Err(std::io::Error::other(format!(
            "rsvg-convert failed with status {status}"
        )));
    }
    Ok(())
}

fn class_durations<N: Analysis<TileLang>>(egraph: &EGraph<TileLang, N>) -> HashMap<Id, i32> {
    let mut duration: HashMap<Id, i32> = HashMap::new();
    for class in egraph.classes() {
        for node in &class.nodes {
            for edge in node.edges() {
                let cid = egraph.find(edge.id);
                duration.entry(cid).or_insert(edge.d);
            }
        }
    }
    duration
}

fn collect_ops<N: Analysis<TileLang>>(
    egraph: &EGraph<TileLang, N>,
    n_resources: usize,
    sol: &SwpSolution,
    duration: &HashMap<Id, i32>,
) -> Vec<Op> {
    let mut ops = Vec::new();
    for (&cid, &(node_idx, t)) in &sol.selected {
        let class = egraph.classes().find(|c| c.id == cid).unwrap();
        let node = &class.nodes[node_idx];
        let name = node.op.as_str().to_string();
        let d = duration.get(&cid).copied().unwrap_or(0);
        if d == 0 {
            continue;
        }
        let rt = &node.rt;
        let resource = (0..n_resources)
            .find(|&s| rt.iter().any(|row| row[s] != 0))
            .unwrap_or(0);
        ops.push(Op { name, t, d, resource });
    }
    ops
}

fn assign_colors(ops: &[Op]) -> HashMap<String, &'static str> {
    let mut color: HashMap<String, &'static str> = HashMap::new();
    for op in ops {
        let i = color.len();
        color.entry(op.name.clone()).or_insert(PALETTE[i % PALETTE.len()]);
    }
    color
}

fn pack_lanes(
    ops: &[Op],
    resource_limits: &[i32],
    ii: i32,
    n_iters: i32,
) -> (Vec<Placed>, Vec<i32>) {
    let n_resources = resource_limits.len();
    let mut events: Vec<(i32, i32, String, usize, i32)> = Vec::new();
    for iter in 0..n_iters {
        for op in ops {
            events.push((op.t + iter * ii, op.d, op.name.clone(), op.resource, iter));
        }
    }
    events.sort_by_key(|e| e.0);

    let mut lane_end: Vec<Vec<i32>> = (0..n_resources)
        .map(|r| vec![i32::MIN; resource_limits[r].max(1) as usize])
        .collect();
    let mut placed = Vec::new();
    for (start, dur, name, resource, iter) in events {
        let lanes = &mut lane_end[resource];
        let lane = lanes
            .iter()
            .position(|&e| e <= start)
            .unwrap_or_else(|| {
                lanes.push(i32::MIN);
                lanes.len() - 1
            });
        lanes[lane] = start + dur;
        placed.push(Placed { resource, lane, start, dur, op: name, iter });
    }
    let lanes_per_resource = lane_end.iter().map(|l| l.len() as i32).collect();
    (placed, lanes_per_resource)
}
