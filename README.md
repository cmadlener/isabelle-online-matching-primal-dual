# Formal Primal-Dual Analysis of Online Matching Algorithms
This repository contains the formal verification of online matching algorithms
using Isabelle/HOL for my Master's Thesis. The formalization of unweighted and
vertex-weighted online bipartite matching follows the proof in [DJK13]. For
AdWords, the formalization is based on the proof in [BJN07].

## Requirements
- [Isabelle 2021-1](https://isabelle.in.tum.de/website-Isabelle2021-1/index.html)
- [AFP 2021-1](https://www.isa-afp.org/release/afp-2022-10-05.tar.gz)

## Bibliography
[DJK13] N. R. Devanur, K. Jain, and R. D. Kleinberg. “Randomized Primal-Dual
analysis of RANKING for Online BiPartite Matching.” In: Proceedings of the
Twenty-Fourth Annual ACM-SIAM Symposium on Discrete Algorithms, SODA
2013, New Orleans, Louisiana, USA, January 6-8, 2013. Ed. by S. Khanna.
SIAM, 2013, pp. 101–107. doi: 10.1137/1.9781611973105.7.

[BJN07] N. Buchbinder, K. Jain, and J. Naor. “Online Primal-Dual Algorithms
for Maximizing Ad-Auctions Revenue.” In: Algorithms - ESA 2007, 15th
Annual European Symposium, Eilat, Israel, October 8-10, 2007, Proceedings.
Ed. by L. Arge, M. Hoffmann, and E. Welzl. Vol. 4698. Lecture Notes in
Computer Science. Springer, 2007, pp. 253–264. doi: 10.1007/978-3-540-
75520-3\_24.
