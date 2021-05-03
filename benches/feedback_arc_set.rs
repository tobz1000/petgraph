#![feature(test)]

extern crate petgraph;
extern crate test;

use test::Bencher;

use petgraph::algo::greedy_feedback_arc_set;

#[allow(dead_code)]
mod common;
use common::digraph;

#[bench]
fn greedy_fas_bench(bench: &mut Bencher) {
    let g = digraph().bigger();

    bench.iter(|| greedy_feedback_arc_set(&g).for_each(|_| ()))
}
