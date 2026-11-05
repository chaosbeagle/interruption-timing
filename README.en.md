# Interruption Timing under Hidden Information

[繁體中文](README.md) · **English** · [日本語](README.ja.md)

Use D.D. Crow (D.D.クロウ) now, or keep it for later? Motivated by a graveyard-removal decision in Yu-Gi-Oh!, this study asks how a player should allocate limited interruptions between immediate and later threats when the opponent holds hidden information.

The paper develops a two-stage model in which each action removes one target. It derives the minimum budget for a guaranteed successful defense and proves:

- If budget $k$ cannot handle all possible states, at most $k+1$ states already witness the conflict.
- If every state has worst-case late demand at least $d$ after all urgent targets are removed, the bound improves to $1+\max(k-d,0)$. Both bounds are sharp.
- Every pair of states can be feasible while three states together are infeasible. Understanding possible opposing hands therefore involves conflicts among several possibilities at once.

[Read the paper](paper/manuscript.pdf) · [LaTeX and TikZ](paper/) · [Lean proofs and theorem correspondence](proofs/README.md)

The core resource bounds, sharp constructions, and counterexamples are formally verified in Lean. The `proofs/` directory provides pinned dependencies and build instructions. Japanese card names appear in the paper's footnotes.

**AI assistance:** GPT-6 Astra assisted with the mathematical derivations in this paper.
