! The flux_elem construct set, distilled: (1) a LOGICAL intent(in) dummy used
! as a bare IF condition, modeled as a Bool input; (2) the generalized
! control-flow join — statements after an if/elseif/else whose branches assign
! LOCALS (some read after the join, some not) and contain nested if-joins of
! their own; (3) a derived-type dummy the body never references (dropped in
! whole-procedure mode, as pointize drops unused params); (4) the `elemental`
! prefix (read past). The siblings pin the neighboring refusals.
module test_kernel_join_locals
  implicit none

  type :: grid_t
    real(8) :: dx
  end type grid_t

contains

  ! Supported: the distilled flux_elem shape. `cfl` is assigned in the first
  ! two branches only (via a nested join) and never read after the outer
  ! join, so it is inlined and dropped; `w` is assigned on every path and
  ! read after the join, so it is merged into one `let`; `q` is an output.
  elemental subroutine face_flux(u, h, h_p1, q, dq, dt, g, vol_cfl, area)
    real(8), intent(in) :: u, h, h_p1, dt, area
    real(8), intent(out) :: q, dq
    type(grid_t), intent(in) :: g
    logical, intent(in) :: vol_cfl
    real(8) :: cfl, w, tmp
    tmp = area * dt
    if (u > 0.0) then
      if (vol_cfl) then ; cfl = u * dt ; else ; cfl = u * area ; endif
      w = h * (1.0 - cfl)
      q = tmp * u * w
    elseif (u < 0.0) then
      if (vol_cfl) then ; cfl = u * dt ; else ; cfl = u * area ; endif
      w = h_p1 * (1.0 - cfl)
      q = tmp * u * w
    else
      q = 0.0
      w = 0.5 * (h + h_p1)
    endif
    dq = tmp * w
  end subroutine face_flux

  ! REFUSAL (functionalize): `w` is assigned on the then-path only, was never
  ! bound before the IF, and is read after the join — undefined on the
  ! fall-through path.
  subroutine partial_local(u, q)
    real(8), intent(in) :: u
    real(8), intent(inout) :: q
    real(8) :: w
    if (u > 0.0) w = u
    q = q + w
  end subroutine partial_local

  ! Supported neighbor: the same shape, but `w` is bound BEFORE the IF, so the
  ! fall-through value is the prior binding (Lean: `let w := if … then u else w`).
  subroutine rebound_local(u, q)
    real(8), intent(in) :: u
    real(8), intent(inout) :: q
    real(8) :: w
    w = 1.0
    if (u > 0.0) w = u
    q = q + w
  end subroutine rebound_local

  ! REFUSAL (printer): a logical LOCAL — only real locals are modeled.
  subroutine logical_local(u, q)
    real(8), intent(in) :: u
    real(8), intent(inout) :: q
    logical :: pos
    pos = u > 0.0
    if (pos) q = q + u
  end subroutine logical_local

  ! REFUSAL (printer): a logical OUTPUT — outputs must be real.
  subroutine logical_out(u, flag)
    real(8), intent(in) :: u
    logical, intent(out) :: flag
    flag = u > 0.0
  end subroutine logical_out

  ! REFUSAL (functionalize): a local read before any assignment.
  subroutine read_unset(u, q)
    real(8), intent(in) :: u
    real(8), intent(inout) :: q
    real(8) :: w
    q = q + w
    w = u
  end subroutine read_unset

  ! REFUSAL (printer): a derived-type dummy that IS referenced in a
  ! per-point kernel — the component read has no rule-B synthesis here.
  subroutine uses_grid(u, q, g)
    real(8), intent(in) :: u
    real(8), intent(inout) :: q
    type(grid_t), intent(in) :: g
    q = q + u * g%dx
  end subroutine uses_grid

end module test_kernel_join_locals
