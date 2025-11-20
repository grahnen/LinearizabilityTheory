# Efficient Linearizability Monitoring

This repository contains the formalized correctness proof of one of the algorithms presented in the paper
[Efficient Linearizability Monitoring](https://dl.acm.org/doi/10.1145/3729328)

So far there is only a proof of correctness for the stack algorithm, which we considered to be the most difficult of them to both design and prove correct.

## Structure
The development is divided into several files. There is still need for restructuring and cleanup, though.

## ListExt
Contains various lemmas about lists that I use.

## Interval
Contains the definition of intervals as structures with two integer endpoints `a, b` accompanied by a proof that `a < b`.

Note that there are no empty intervals.

## IntervalSet
A set of intervals as a list of `Interval`s that are ordered and nonoverlapping.

## AssocMap
Associative map with some additional constraints. It is implemented as a list of pairs `Nat * V`.
Additionally, we require that the keys are sorted, and that a predicate `P v1 v2` holds for every pair of distinct `k1, k2` for `(k1, v1), (k2, v2)` in the map.

## Value
A value consists of two intervals, `add` and `rmv`, that are separated by `add.b < rmv.a`.

## History
A history is an `AssocMap` with keys of type `Value`.

## Linearizability
First, we define `seq` to be lists of events, where events are either `add` or `rmv` for a given `Nat` value.

We define what it means for a sequence `s` to be a stack sequence by means of an inductive predicate.

We define a sequentialization as a permutation of the /events of `H`/ that respects the imposed orderings of intervals on the values in `H`.

A linearization is a sequentialization that is a stack sequence.

## CompatAlg
Here we start developing specifics that are used in the proof for the algorithm.

## CorrectAlt
Here we implement the algorithm and prove its correctness.