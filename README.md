# Whitney-Graustein Theorem Formalization in Lean 4

Welcome to the formalization of the Whitney-Graustein Theorem in Lean 4. This project contains a rigorous implementation of the theorem using the Lean theorem prover.

## Overview

### What is the Whitney-Graustein Theorem?

The Whitney-Graustein Theorem is a fundamental result in differential topology. It states that two smooth immersions of the circle into the plane are homotopic through immersions if and only if they have the same turning number. This theorem plays a crucial role in the classification of planar curves and sphere eversion (turning a sphere inside out!).

### Structure and Definitions

The formalization is based on these core structures and components:

- **`CircleImmersion`**: A structure representing a smooth immersion of the circle into the complex plane.
- **`HtpyCircleImmersion`**: A structure representing a homotopy through circle immersions.
- **`WG_pair`**: A structure representing a pair of circle immersions satisfying the Whitney-Graustein theorem's assumptions.

### Key Lemmas and Proofs

1. **`root_lemma_maybe`**: Establishes the existence of an `N₀` such that for all `N` greater than `N₀`, a certain inequality involving parameters holds true.
2. **`ruffle` and `ρ`**: Two functions that help to construct the homotopy explicitly.
3. **`γ`**: Represents the homotopy between the two circle immersions.
4. **`bro_on_god₀`** and **`bro_on_god₁`**: Critical technical lemmas in establishing the non-zero derivative property of the homotopy. (It was really late at night when I did this part...)

### Main Theorem

- **`whitney_graustein`**: The main theorem implementation. It shows that given two circle immersions with the same turning number, there exists a homotopy through circle immersions between them.

## Project Layout

- **`.lake`**: Standard Lean+Mathlib libraries that provide foundational structures.
- **`WhitneyGraustein`**:
  - `calculus.lean`: Contains useful lemmas and utilities for the main theorem and proof
  - `WG-main.lean`: Statement and proof of the main theorem
  
### How to Use

1. Install [Lean](https://leanprover.github.io/) and [Mathlib](https://leanprover.github.io/mathlib4/).
2. Clone this repository.
3. Explore the theorem formalization by reading the `WG-main.lean` file and the lemmas leading up to it.
4. Test your understanding by experimenting with Lean's interactive features and verifying individual lemmas.

### References

- [Lean Prover Documentation](https://leanprover.github.io/)
- [Mathlib4 Library Documentation](https://leanprover.github.io/mathlib4_docs/)

### Acknowledgements
This formalization is created by Riyaz Ahuja and Leo Stephenson. Special thanks to Patrick Massot for the guidance and inspiration behind this project.
