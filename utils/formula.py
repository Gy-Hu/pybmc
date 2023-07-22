from pathlib import Path
import string
from typing import Union, List
import json

import networkx
import z3

PathLike = Union[Path, str]


def from_z3(smt_formula) -> 'CNFFormula':
    """
    Convert a Z3 expression to a CNF formula.

    :param smt_formula: Z3 expression (all types that can be fed to a Goal instance)
    :return: a CNF Formula instance
    """
    f = CNFFormula()
    f.goal.add(smt_formula)
    f._apply_tactics()
    return f

class CNFFormula:
    """
    Class the represent a CNF formula in DIMACS format.
    It can either be populated by a CNF file or by an SMT2
    file. In this later case Z3 is used to parse the file
    and to extract the CNF representation.
    """
    def __init__(self):
        """
        Class construction. A formula is meant to be instanciated
        via the static methods from_z3, from_smt2_file, from_dimacs_string
        and from_dimacs_file.
        """
        self.goal = z3.Goal()
        self.tactics = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')
        self.subgoal = None  # keep it in case of
        # Goal is a collection of constraints we want to find a solution or show to be unsatisfiable (infeasible).
        # Goals are processed using Tactics. A Tactic transforms a goal into a set of subgoals.
        # A goal has a solution if one of its subgoals has a solution.
        # A goal is unsatisfiable if all subgoals are unsatisfiable.

        self.variables_num = None
        self.clauses_num = None
        self.clauses = []

    def _apply_tactics(self) -> None:
        """
        Apply the Z3 tactics to generate the goals.

        :return: None
        """
        self.subgoal = self.tactics(self.goal)
        assert len(self.subgoal) == 1, "warning: multiple subgoal for the formula"
        # if len(self.subgoal) > 1:
        #     print("warning: multiple subgoal for the formula")

    


    def to_dimacs_file(self, output_file: PathLike) -> None:
        """
        Write the CNFFormula to a DIMACS file. If it was instanciated
        from z3 just call .dimacs() otherwise dump all the clauses.

        :param output_file: DIMACS output file
        :return: None
        """
        with open(output_file, "w") as f:
            if self.subgoal:
                f.write(self.subgoal[0].dimacs())
            else:
                assert False, "warning: no subgoal to write"

    def to_dimacs_string(self):
        """
        Write the CNFFormula to a DIMACS file. If it was instanciated
        from z3 just call .dimacs() otherwise dump all the clauses.

        :param output_file: DIMACS output file
        :return: None
        """
        if self.subgoal:
            return [self.subgoal[0].dimacs()]
        else:
            assert False, "warning: no subgoal to write"
