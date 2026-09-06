! A COLUMN kernel distilled from MOM_continuity_PPM's set_zonal_BT_cont — the
! B2 constructs of docs/COLUMN_KERNELS.md: MASKED nests (`do concurrent
! (i=…, do_i(i,j))` under a plain `do k`: the mask is a per-column Bool input,
! a masked fold step keeps its state), ROW-SCRATCH locals (`dul(i)`, indexed
! by one column index under the plain `do j`; per-column scalars, initialized
! before they are read), a FOLD with SEVERAL state variables (`let (fa_l, uh_l)
! := ks.foldl (fun (fa_l, uh_l) k => …)`), a per-column IF at the column level
! whose branches write COMPONENT ARRAYS of an intent(inout) derived-type dummy
! (per-column outputs named after the components), an `if / elseif` join whose
! two locals read each other's prior values (bound together by one
! destructuring let), and a local re-assigned after an output read it (the
! output's pending value is let-bound before the name is shadowed). The
! siblings pin the boundary: a masked map, a row scratch read before it is
! written, a row scratch shared by concurrent columns, a component write
! inside a k-loop, and a masked nest in a POINT kernel.
module test_kernel_bt_cont
  implicit none

  type :: grid_t
    real(8), allocatable :: dx(:,:)
  end type grid_t

  type :: cont_t
    real(8), allocatable :: fa_w(:,:), fa_e(:,:), ubt(:,:)
  end type cont_t

contains

  ! The banked point primitive (two intent(out) results).
  elemental subroutine flux_pt(u, h, q, dq, dt)
    real(8), intent(in) :: u, h, dt
    real(8), intent(out) :: q, dq
    q = u * h * dt
    dq = h * dt
  end subroutine flux_pt

  ! Supported: the column kernel (columns = j, i).
  subroutine bt_cont(u, h, cont, du0, dt, g, n, m, nz, do_i)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(0:n, m, nz), h(0:n+1, m, nz), du0(0:n, m)
    real(8), intent(in) :: dt
    type(grid_t), intent(in) :: g
    type(cont_t), intent(inout) :: cont
    logical, intent(in) :: do_i(0:n, m)
    real(8) :: dul(0:n), fa_l(0:n), uh_l(0:n)
    real(8) :: u_l, q_l, dq_l, fa_0, fa_avg, cfl_min, idt
    integer :: i, j, k
    idt = 1.0 / dt ; cfl_min = 1e-6
    do j = 1, m
      do concurrent (i = 0:n)
        dul(i) = max(0.0, du0(i,j) + (cfl_min * idt) * g%dx(i,j))
        fa_l(i) = 0.0 ; uh_l(i) = 0.0
      end do
      do k = 1, nz ; do concurrent (i = 0:n, do_i(i,j))
        if (u(i,j,k) + dul(i) < 0.0) dul(i) = -u(i,j,k)
      end do ; end do
      do k = 1, nz ; do concurrent (i = 0:n, do_i(i,j))
        u_l = u(i,j,k) + dul(i)
        call flux_pt(u_l, h(i+1,j,k), q_l, dq_l, dt)
        fa_l(i) = fa_l(i) + dq_l
        uh_l(i) = uh_l(i) + q_l
      end do ; end do
      do concurrent (i = 0:n)
        if (do_i(i,j)) then
          fa_0 = fa_l(i) ; fa_avg = fa_l(i)
          if ((dul(i) - du0(i,j)) /= 0.0) fa_avg = uh_l(i) / (dul(i) - du0(i,j))
          if (fa_avg > fa_0) then ; fa_avg = fa_0
          elseif (fa_avg < 0.5 * fa_0) then ; fa_0 = fa_avg ; endif
          cont%fa_w(i,j) = fa_0
          fa_0 = 0.0
          cont%fa_e(i,j) = fa_avg - fa_0
          cont%ubt(i,j) = 1.5 * (dul(i) - du0(i,j))
        else
          cont%fa_w(i,j) = 0.0 ; cont%fa_e(i,j) = 0.0 ; cont%ubt(i,j) = 0.0
        endif
      end do
    end do
  end subroutine bt_cont

  ! REFUSAL: a masked map — the cells of skipped iterations stay unwritten.
  subroutine masked_map(u, w, n, m, nz, do_i)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(out) :: w(n, m, nz)
    logical, intent(in) :: do_i(n, m)
    integer :: i, j, k
    do concurrent (k = 1:nz, j = 1:m, i = 1:n, do_i(i,j))
      w(i,j,k) = 2.0 * u(i,j,k)
    end do
  end subroutine masked_map

  ! REFUSAL: a row scratch carried into a fold before any column wrote it.
  subroutine scratch_read_first(u, s, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(out) :: s(n, m)
    real(8) :: acc(n)
    integer :: i, j, k
    do j = 1, m
      do k = 1, nz ; do concurrent (i = 1:n)
        acc(i) = acc(i) + u(i,j,k)
      end do ; end do
      do concurrent (i = 1:n)
        s(i,j) = acc(i)
      end do
    end do
  end subroutine scratch_read_first

  ! REFUSAL: a row scratch shared by columns that run concurrently (a race).
  subroutine scratch_racing(u, s, n, m)
    integer, intent(in) :: n, m
    real(8), intent(in) :: u(n, m)
    real(8), intent(out) :: s(n, m)
    real(8) :: t(n)
    integer :: i, j
    do concurrent (j = 1:m)
      do concurrent (i = 1:n)
        t(i) = 2.0 * u(i,j)
        s(i,j) = t(i)
      end do
    end do
  end subroutine scratch_racing

  ! REFUSAL: a component-array write inside a k-loop.
  subroutine comp_write_in_k(u, cont, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(0:n, m, nz)
    type(cont_t), intent(inout) :: cont
    integer :: i, j, k
    do j = 1, m
      do k = 1, nz ; do concurrent (i = 0:n)
        cont%ubt(i,j) = u(i,j,k)
      end do ; end do
    end do
  end subroutine comp_write_in_k

  ! REFUSAL (point tier): a masked do concurrent has no pointwise model.
  subroutine masked_point(u, w, n, m, nz, do_i)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(inout) :: w(n, m, nz)
    logical, intent(in) :: do_i(n, m)
    integer :: i, j, k
    do concurrent (k = 1:nz, j = 1:m, i = 1:n, do_i(i,j))
      w(i,j,k) = 2.0 * u(i,j,k)
    end do
  end subroutine masked_point

end module test_kernel_bt_cont
