# Notes for Claude: Codex UPhi branch

Date: 2026-07-08

Codex worked on the assigned u-slice branch:
`prop:uphi-reduce` / `prop:uphi-codim3` / `cor:uphi-exhausted`.

## What landed

Commit `f4b7878` adds the Tier 1 analytic zero-set part:

- `Appendix/AnalyticBridge/D34_UPhi_Branch.thy`
- `M5_Dev_UPhi/ROOT`
- `M5_Dev_UPhi/Scratch_UPhi.thy`

The proved names are:

- `F_eta`
- `real_analytic_on_F_eta`
- `F_eta_at_0`
- `F_eta_zeros_nowhere_dense`

The zero-set theorem uses the already-proved
`real_analytic_1d_nowhere_dense_zeros` on `UNIV`, with witness `u = 0` from
`F_eta_at_0`.

Verified builds before commit/push:

- `Applied_Math_M5_UPhi` BUILD_EXIT=0
- `Applied_Math_D34_Analytic` BUILD_EXIT=0

## Architecture note

`PARALLEL_WITH_CODEX.md` asked for a permanent UPhi session rooted at
`Appendix/AnalyticBridge`, but Isabelle rejects duplicate session directories
because `Applied_Math_D34_Analytic` already owns that directory.  The buildable
compromise is:

- keep the permanent branch file at `Appendix/AnalyticBridge/D34_UPhi_Branch.thy`;
- register it as a separate theory in the existing `Applied_Math_D34_Analytic`
  session;
- do not edit `Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`.

## Tier 2 status

Tier 2 is now partially advanced.  The invariant derivative substrate has been
added to `D34_UPhi_Branch.thy` and mirrored in `M5_Dev_UPhi/Scratch_UPhi.thy`:

- `DM_paper_x_slot_1`
- `DM_paper_x_slot_2`
- `DM_paper_x_slot_3`
- `Phi_par_slot_value`
- `Phi_par_parallel_slot_value`

These expose the actual Fréchet derivative of `Phi_par` in a general slot and
in the parallel slot `slot m (cvec_dip omega0 omegas omega)`.

The remaining Tier 2 work is the gauge dictionary/algebra:

- connect the resulting expression to the paper's
  `F_eta u = cos(kappa*u) - kappa*(u-eta)*sin(kappa*u)` under the gauge
  hypotheses (`b = 0`, `Phi = 0`, `a > 0`, `eta = g1/(2g)`);
- if the full statement does not come together cleanly, use a precisely stated
  `sorry` in `D34_UPhi_Branch.thy` with a `NEEDS:` block instead of blocking
  Tier 1.

The relevant bridge names already available:

- `slot`
- `d_A_moment_x_slot`
- `d_M1_moment_x_slot`
- `d_M2_moment_x_slot`
- `d_M11_moment_x_slot`
- `d_M12_moment_x_slot`
- `d_M22_moment_x_slot`
- `Phi_par`
- `e_par`
- `Dcvec_dip_e_par`
- `has_derivative_gradU_dip_x_explicit`

The shared bridge file was not modified by Codex.

## Tier 2 pointwise reduction status

Follow-up UPhi work extends Tier 2 beyond the derivative substrate.  The branch
now adds:

- `ucoord`
- `eta_par`
- `uphi_E1_deriv_F_eta`
- `uphi_scalar_zero_iff`
- `Phi_par_parallel_slot_F_eta_identification`
- `uphi_reduce_pointwise`

`uphi_reduce_pointwise` is the usable pointwise `prop:uphi-reduce` shape:
under the c-adapted branch hypotheses (`det Dcvec != 0`, `c != 0`,
`Im (M_1) = 0`, `Phi_par = 0`, `a > 0`, `gain_dip > 0`), the parallel-slot
derivative vanishes iff `F_eta eta kappa u = 0`.

There is exactly one intentional upstream placeholder:
`Phi_par_parallel_slot_F_eta_identification`.  It isolates the missing
c-adapted gauge dictionary from the invariant derivative formula
`Phi_par_parallel_slot_value` to the scalar paper expression
`-2*a*gain*kappa*F_eta eta kappa u`.  Everything downstream of that identity is
proved, including the nonzero-factor cancellation.

Builds checked during implementation:

- `Applied_Math_M5_UPhi` BUILD_EXIT=0
- `Applied_Math_D34_Analytic` BUILD_EXIT=0
