This project implements a set (inclusion) constraint solver.

Set constraints are a convenient and efficient way to specify and
solve problems that can be expressed as graph reachability.  This
implementation represents the constraint graph in *inductive* form,
which trades solving time (the constraint system is solved faster and
in less space) for solution extraction time (looking up the solution
for a given set variable is slightly more expensive than in standard
form).

See the Constraints.Set.Solver module for more thorough documentation
and usage examples.
