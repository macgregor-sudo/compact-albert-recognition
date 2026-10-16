# Selected theorem statements

The following entries describe the 23 declarations selected in comparator.json, in the same order. Unless a namespace is printed otherwise, names are prefixed by Glennie.SubmissionR03. Definitions use the raw trace T(1)=3, half Jordan product, and raw pairing B(x,y)=T(x circle y). An actual frame has three trace-one orthogonal idempotents summing to the unit. A configuration has three ordered frames and retains all nine labels. “Admitted” refers to the proved open neighborhood in the fixed twenty-coordinate affine chart of full trace data. The Lean name fullLedger denotes the complete 54-entry trace list.

1. q26_eq_iff_fullLedger_eq. For any two actual ordered frame triples, equality of the specified Q26 lists is equivalent to equality of all 54 pair and triple traces.

2. division_free. For arbitrary three Albert elements, the specified six-reading weighted score equals twice Phi. This is an algebraic identity with no input-dependent denominator or admissibility premise.

3. score_eq_two_phi. The same identity holds when the three inputs are the fixed frame encoders; the statement itself does not require frame axioms.

4. atoms_generate_of_score. If an actual frame triple has nonzero score, every real Jordan-product-closed subspace containing its nine idempotents is the whole Albert algebra. The unit is recovered from a frame sum.

5. nearby_sign_rigidity. Near the flat reference of the 54-entry trace list, two actual frame triples with equal full trace lists and the same strict Phi sign differ by one simultaneous product-and-trace automorphism.

6. nearby_fibres_two_orbits. There is an open chart neighborhood of the flat reference such that each entire admitted fiber is exactly two disjoint automorphism orbits. Both have continuous actual-frame representatives with exact prescribed traces and strict opposite Phi signs. The centered chart fibers equal the decoded full-trace-list fibers.

7. q20_eq_iff_fullLedger_eq. Removing the six fixed entries of Q26 leaves Q20 with the same equality fibers on actual frames. Q20 and the centered affine chart encode20 are distinct maps.

8. near_flat_scalar_margin. Some open full-trace-list neighborhood of the flat reference has |Phi|>1/27 on every actual frame triple in its preimage.

9. signed_readout_margin. Six absolute scalar-reading error bounds of size epsilon, with epsilon nonnegative and observed weighted-score magnitude greater than 12epsilon, certify the strict sign of Phi.

10. finite_word_marked_recognition. In any real inner-product space with a bilinear product, a distinguished element and three marks, exact native matching of the 27-word Gram table, product-word pairings, and full product squared norms gives a unique injective linear map from Albert preserving the unit, marks, product and pairing, whose range is their generated subspace. Unused ambient directions are allowed.

11. local_q26_score_orbit_test. On a proved admitted local domain, the score never vanishes, and equality of Q26 together with equality of strict score sign is equivalent to simultaneous automorphism equivalence.

12. phi_nonzero_generation_stabilizer. For arbitrary Albert elements x,y,z with Phi nonzero, every real product-closed subspace containing 1,x,y,z is the whole algebra. An automorphism fixing x,y,z is the identity; a Jordan derivation annihilating them is zero.

13. compact_local_phi_margin. Every compact subset of a suitable admitted chart has a positive uniform absolute Phi margin for all actual frame triples above it.

14. compact_feasible_element_recovery. Continuous signed actual-frame sections recover configurations uniformly on compact feasible chart regions: sufficiently close feasible coordinates give arbitrarily close corresponding idempotents after one simultaneous automorphism, using the correct sign branch. The tolerance is existential.

15. compact_noisy_feasible_element_recovery. The same type of recovery uses the sign of the noisy six-reading score when its strict error margin holds. The theorem supplies continuity and opposite strict signs for the same sections used in the recovery statement. Both chart points remain feasible and in the stated compact region.

16. six_readout_displaced_generation. Write Phi_observed = S_observed/2. If raw reading errors fit a nonnegative scalar allowance xi and both original and displaced triples have raw norm at most R, corresponding displacements at most delta preserve sign, unital generation and trivial pointwise stabilizer whenever 18R^8 delta < |Phi_observed|-xi. The reading allowance requires 6epsilon <= xi. No frame premise is needed for this statement about encoded inputs and their displacements.

17. diagonalN_defect_response_radius. For any finite coordinatewise Euclidean target and any supplied exact real linear isometry f, a uniform relative product defect at most mu on every source pair implies |Phi(x,y,z)| <= 38mu R^9 on every raw radius-R triple, with mu,R nonnegative.

18. frame_noisy_diagonalN_defect_lower. For an actual frame triple, the same target and all-input defect premise imply (|S_observed|-12epsilon)/(1216sqrt(2)) <= mu. The lower bound is informative when the observed margin is positive.

19. frame_noisy_represented_defect_lower. The same noisy lower bound holds for a target supplied with an isometric linear representation into a normed associative real algebra, a symmetrized-product identity, and a linear cyclic functional reproducing the inner product. These are explicit premises. A normalized positive tracial state is not assumed; a concrete symmetric-matrix instance is not supplied by this result.

20. Glennie.SubmissionR04Quotient.admitted_orbit_quotient_homeomorph. For a suitable open admitted chart V, the actual simultaneous automorphism quotient is homeomorphic to V times a two-point sign set, and the homeomorphism agrees with the specified trace-list/sign invariant.

21. Glennie.SubmissionR04Intrinsic.intrinsic_local_reconstruction. Let E be a finite-dimensional complete real normed space with a symmetric cubic normalized at e. Require the normalized log-Hessian at e to be positive definite on the entire ambient vector space. If a tangent linear equivalence preserves the metric and full vector-valued curvature of the Albert model, the output constructs an algebra equivalence A and a local chart V. It preserves unit, cubic, raw trace, pairing and reconstructed product, identifies the metric, ambient connection coefficient and ambient curvature at e, and transports the local two-orbit theorem, score completeness, trace-list equivalence and, for admitted frame triples, generation, stabilizers and derivation vanishing. Its result record is constructed, not assumed. The output equivalence need not extend the supplied tangent map.

22. Glennie.Compact.GlennieFullDerivativeR01.hasFDerivAt_phiTriple. For every native Albert triple, the actual full Frechet derivative on J^3 is the continuous linear functional displayed below. The domain includes all ambient directions.

23. Glennie.Compact.GlennieFullDerivativeR01.eq_top_of_fderiv_phiTriple_ne_zero. If a real linear subspace K contains 1,x,y,z, is closed under the native Jordan product, and the full ambient derivative of Phi at (x,y,z) is nonzero, then K=J. This does not require Phi nonzero. The converse is outside this selection.

Write K_xy=U_x U_y-U_y U_x and p=x circle y. Use the explicitly normalized triple product

    {a,b,c}=2(a circle(b circle c)+(a circle b)circle c-(a circle c)circle b),
    G(x,y,z)={K_xy z,z,p}-K_xy(U_z p).

For every x,y,z in J and every ambient direction (a,b,c), the selected derivative theorem gives

    D Phi_(x,y,z)(a,b,c)
      = B(a,G(y,z,x))+B(b,G(z,x,y))+B(c,G(x,y,z)).

Here B is the raw trace pairing; no factor of 1/3 is absorbed into G. This is the actual Frechet derivative on the full ambient space J^3, not a derivative restricted to frames or to a single input slot. If it is nonzero, every real linear subspace containing 1,x,y,z and closed under the Jordan product equals J. Thus, if the full derivative is nonzero, x,y,z together with the unit generate J. No Phi-nonzero or local-frame premise is required. The converse is outside the selected statements. [Selected statements 22–23; declaration names and source files in formalization.yaml.]

In entry 21, positivity is the fixed-basepoint premise g_e(x,x)>0 for every nonzero x in E, with g_e=-(1/3)D^2(log N)_e. It is imposed on the entire ambient vector space, rather than only ker(DN_e), and does not assert positivity at every point.

The exact statements and proof providers are the source of these accounts. Selected material is adapted from unpublished notes on compact Albert reconstruction and finite observations. Classical background references are placed at the relevant claims in INTRODUCTION.txt; those references are not substitutes for the local frame theorem or the recognition statements.

Statements 22–23 are defined in Glennie/Compact/GlennieFullDerivativeR01.lean and exported through Solution.R05DerivativeExtension, whose public import chain passes through Glennie.Compact.EasyFirstIntegratedR01. The metadata defining-file and exporting-module fields therefore refer to different locations.
