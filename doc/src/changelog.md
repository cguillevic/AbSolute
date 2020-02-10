# Changelog

We describe the main changes operated in each version of AbSolute.
This is especially useful when analyzing the results in [kobe-database](https://github.com/ptal/kobe-database).

Version 0.8.0:
  * Add an `embed` function which is the inverse of `project` in abstract domain, it increases the efficiency of the HC4 algorithm.
  * Fix the min/max filtering in interval.
  * New converter between bounds to avoid always going through rational when converting a bound.

Version 0.7.0:
  * Add the propagator completion domain transformer, which equips any projection-based abstract domain with propagators.
  * The box domain does not contain anymore its constraints.
  * Fix a bug when selecting the new bounds in the branch-and-bound algorithm.

Version 0.6.0:
  * New architecture of products based on abstract domain sharing.
  * Typing of the logic formula according to the type of an abstract domain.
  * Note: this version was bugged due to a problem in the BAB algorithm (fixed in 0.7.0).