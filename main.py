from typing import Dict, List
import numpy as np
import sympy as sp


# `g` is the arithmetic version of `phi`.
x1, x2, x3, x4 = sp.symbols("x1, x2, x3, x4")
g = sp.Poly((1 - x1) * x2 * ((x3 + x4) - (x3 * x4)), x1, x2, x3, x4)


# Helper function
def get_variables(v: int) -> List:
    """Creates a list of `v` variables named x1, x2, ... x`v`.

    Args:
      v: The number of variables in `g`

    Returns:
      List of variables in `g`. E.g. [x1, x2, ..., xv]
    """
    ret_val = []
    for i in range(1, v + 1):
        ret_val.append(eval(f"x{i}"))

    return ret_val


class Prover:
    def __init__(self, g: sp.Poly, F: int) -> None:
        """Initializes P with the arithmetic function `g`.

        Args:
          g: The Boolean-valued function that we will apply sum-check to.

        Returns:
          None
        """
        self.g = g
        self.F = F
        self.num_vars = self.rounds = len(g.free_symbols)
        self.variables = get_variables(self.num_vars)

    def getSum(self, round: int, r: List) -> sp.Poly:
        """Calculates the sum of `g`.

        Args:
          round: The round of the protocol.
          r: Random challenge(s) from Verifier.
          F: Finite field selection. This is the security parameter.

        Returns:
          Sum of `g`. During round 0, the sum will be an integer (degree-0 polynomial).
            In all other rounds, the sum will be a monomial.
        """
        # For debugging/intuition
        print(f"\nRound {round}")

        # Helper function to convert an integer to binary string with `n`
        #   leading zeros
        getbinary = lambda x, n: format(x, "b").zfill(n)

        # Number of variables to sum over a Boolean hypercube
        free_vars = self.rounds - round

        # Initialize the sum to zero
        g_j = sp.Poly(0, x1)
        # Sum the assigned function `g` over the Boolean hypercube
        for input_int in range(2**free_vars):
            input_bin = getbinary(input_int, free_vars)
            assignments = {}
            for bit, var in zip(input_bin, self.variables[round:]):
                assignments[var] = bit
            print(f"g_j before bit subs: {g_j}")
            # Substitute variable names for bit assignments,
            #   evaluate `g` and accumulate result in `g_j`
            g_j += self.g.subs(assignments)
            g_j = g_j
            print(f"g_j after bit subs: {g_j}")

        # Printing for debugging/intuition
        print(f"\ng_j before random subs: {g_j}")
        print(f"random {r}")
        if round > 1:
            g_j = g_j.subs(r)
            print(f"g_j after random subs: {g_j}")

        return g_j.set_modulus(self.F)

class Verifier:
    def __init__(self, g: sp.Poly, oracle: sp.Poly, F: int) -> None:
        """Initializes Verifier.

        Args:
          g: The arithmetic function to use for the protocol.
          oracle: Must execute `g` one time with a random input vector.
          F: Finite field selection. This is the security parameter.

        """
        self.F = F
        self.g = g
        # In sum-check, the verifier must be able to make one call to an oracle
        self.oracle = oracle
        self.num_vars = self.rounds = len(g.free_symbols)
        self.variables = get_variables(self.num_vars)
        self.challenges = np.random.randint(F, size=len(self.variables))

    def getRandom(self, round: int) -> List:
        """Gets random variable assignments to send to Prover.

        Args:
          round: Current round number of protocol.

        Returns:
          List of random values.
        """
        random = {}
        for rnd in range(round - 1):
            random[self.variables[rnd]] = self.challenges[rnd]
        return random

    def executeSumCheck(self, prover: Prover) -> None:
        """Allows a verifier to execute the sum-check protocol.

        Args:
          prover: Instance of a Prover object.

        Returns:
          None
        """
        for round in range(self.rounds + 1):
            random = self.getRandom(round)
            g_j = prover.getSum(round, random)

            if round > 0:
                # Must cast `g` to a SymPy Polynomial for some reason.
                g_j = sp.Poly(g_j)

                # Check that g_j is univariate
                assert len(g_j.free_symbols) <= 1

                # Check that g_j is of degree at most deg_j(g)
                assert sp.degree(g_j, gen=self.variables[round - 1]) <= sp.degree(
                    self.g, gen=self.variables[round - 1]
                )

            if round == 0:
                # Save the claimed answer for printing
                C1 = g_j
            elif round == 1:
                assert last_g_j == (g_j(0) + g_j(1)) % self.F
            elif round > 1:
                assert last_g_j.subs(random) % self.F == (g_j(0) + g_j(1)) % self.F
            last_g_j = g_j

        random = self.getRandom(self.rounds + 1)
        assert last_g_j.subs(random) % self.F == self.oracle.subs(random) % self.F
        print(f"Sum-check passed! Answer is {C1}")

# Select finite field
F = 16

# Instantiated prover and verifier objects
P = Prover(g, F)
V = Verifier(g, g, F)

# Execute the sum-check protocol
V.executeSumCheck(P)
