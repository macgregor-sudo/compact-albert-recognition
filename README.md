# Finite Observations and Recognition of the Compact Albert Algebra

Let J=H_3(O), the real algebra of 3×3 Hermitian matrices over the division octonions, with product a∘b=(ab+ba)/2 and diagonal trace T. A frame p=(p_0,p_1,p_2) consists of trace-one elements satisfying p_i∘p_i=p_i, p_i∘p_j=0 for i≠j, and p_0+p_1+p_2=1. For frames p,q,r, record the 27 pair traces T(p_i∘q_j), T(q_j∘r_k), T(r_k∘p_i), and 27 triple traces T((p_i∘q_j)∘r_k), for i,j,k∈{0,1,2}. How much do these traces determine?

Each trace list in some open neighborhood of the data with pair entries 1/3 and triple entries 1/9, in a fixed twenty-dimensional chart, determines exactly two equivalence classes. Equivalence means one product-and-trace-preserving real linear bijection acting on all nine labeled elements, without relabeling. The sign of the degree-nine scalar Phi distinguishes the classes. With x=p_2−p_0, y=q_2−q_0, z=r_2−r_0, define

B(a,b) = T(a∘b),
U_a(b) = 2a∘(a∘b)−(a∘a)∘b,
Phi(x,y,z) = B((U_x U_y−U_y U_x)z,U_z(x∘y)).

Phi's derivative uses Glennie's degree-eight vector polynomial.

For arbitrary x,y,z∈J, Phi≠0 implies that 1,x,y,z generate J.

Recognition starts from a homogeneous cubic N on finite-dimensional real normed E, with N(e)=1 and g_e=−(1/3)D²(log N)_e positive definite on all E. A supplied linear equivalence ker(DN_e)≃ker T (the trace-zero subspace), matching g_e to B/3 and full vector-valued curvature tensors, yields an Albert algebra equivalence.

Consider 27 fixed parenthesized products of a distinguished element and three chosen elements in a real inner-product space with bilinear multiplication. Exact matching with the Albert table of pairwise inner products, inner products of products with these expressions and full ambient squared product norms determines a unique isometric, product-preserving linear embedding of J onto the subspace they generate under products and linear combinations, preserving the distinguished element and chosen elements.

Further results give error bounds.

## Reading the results

[ABSTRACT.txt](ABSTRACT.txt) gives the compact account; [INTRODUCTION.txt](INTRODUCTION.txt)
develops the definitions, examples and scope. [THEOREMS.md](THEOREMS.md) describes the 23
selected statements, and [formalization.yaml](formalization.yaml) maps them to their Lean
declarations. [PROVENANCE-AND-RELATED-WORK.txt](PROVENANCE-AND-RELATED-WORK.txt) explains
the classical sources and which conclusions are specific to this formalization.

The reconstruction result is local in a fixed twenty-dimensional chart. The curvature
recognition result requires the supplied tangent metric and full curvature equivalence;
the finite-word recognition result requires exact table agreement. Global orbit
classification, the converse of the derivative generation criterion, approximate-table
recognition and a physical measurement implementation are outside the selected results.

## Formalization and verification

The project uses Lean 4.35.0-rc2 and the exact Mathlib revision in `lake-manifest.json`.
`comparator.json` specifies the Challenge and Solution modules, the 23 selected names
and the permitted axioms. The metadata links each declaration to its source file.
The Challenge contains specification holes; the
selected Solution proof closures have none.

The 23 selected statements passed a Linux verification run on 16 October 2026 using Comparator, the default Lean kernel, NanoDa and con-ron. The permitted axioms were propext, Classical.choice and Quot.sound. This release changes only comments in the Lean sources from that run; all non-comment content is unchanged. No new build or checker run is claimed for the revised files. Prose and metadata are outside that proof check. No Palomar acceptance or independent human mathematical review is claimed.

## Authorship and collaboration

All project exposition and Lean code are AI-generated under Robert MacGregor's direction. Robert is a non-mathematician and welcomes mathematical collaboration: macgregor@gmail.com. No novelty is asserted.

[AUTHORSHIP-AND-AUTOMATION.txt](AUTHORSHIP-AND-AUTOMATION.txt) gives the model-provenance
disclosure. Reused code and dependencies retain their original credits and licenses;
see [THIRD-PARTY-NOTICES.md](THIRD-PARTY-NOTICES.md). Project code is licensed under
[Apache-2.0](LICENSE).
