! The continuity_convergence construct set, distilled: (1) a READ-ONLY NEIGHBOR
! STENCIL — `flux(i-1,j,k)` next to `flux(i,j,k)` on an array the nest never
! writes, becoming the synthesized input `flux_im1` (admitted in `do
! concurrent` nests only); (2) a component array of an intent(in) derived-type
! dummy indexed by a SUBSET of the loop indices (`g%iarea(i,j)` in a k,j,i
! nest), becoming a per-cell input; (3) a nest-invariant LOCAL (`h_min`, set
! before the loop and only read inside it), becoming an input; (4) OPTIONAL
! intent(in) dummies referenced by the addressed nest (their presence tests
! sit outside it). The siblings pin the refusals at the new boundary.
module test_kernel_stencil
  implicit none

  type :: grid_t
    real(8), allocatable :: iarea(:,:)
  end type grid_t

contains

  ! Supported: nest 1 (inside the presence guard) is the distilled
  ! continuity_zonal_convergence body.
  subroutine converge(h, flux, dt, g, n, m, nz, h_in, hmin_opt)
    type(grid_t), intent(in) :: g
    integer, intent(in) :: n, m, nz
    real(8), intent(inout) :: h(n, m, nz)
    real(8), intent(in) :: flux(0:n, m, nz)
    real(8), intent(in) :: dt
    real(8), intent(in), optional :: h_in(n, m, nz)
    real(8), intent(in), optional :: hmin_opt
    real(8) :: h_min
    integer :: i, j, k
    h_min = 0.0
    if (present(hmin_opt)) h_min = hmin_opt
    if (present(h_in)) then
      do concurrent (k=1:nz, j=1:m, i=1:n)
        h(i,j,k) = max(h_in(i,j,k) - dt * g%iarea(i,j) * (flux(i,j,k) - flux(i-1,j,k)), h_min)
      end do
    end if
  end subroutine converge

  ! REFUSAL: the same stencil in a plain DO nest — admitted in do concurrent
  ! nests only (the plain-DO schema-lemma variant is not yet proved).
  subroutine stencil_plain_do(h, flux, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(inout) :: h(n, m, nz)
    real(8), intent(in) :: flux(0:n, m, nz)
    integer :: i, j, k
    do k = 1, nz
      do j = 1, m
        do i = 1, n
          h(i,j,k) = flux(i,j,k) - flux(i-1,j,k)
        end do
      end do
    end do
  end subroutine stencil_plain_do

  ! REFUSAL: a neighbor read of the array the nest WRITES — a cross-iteration
  ! recurrence, whatever the loop form says.
  subroutine stencil_written(h, flux, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(inout) :: h(0:n, m, nz)
    real(8), intent(in) :: flux(n, m, nz)
    integer :: i, j, k
    do concurrent (k=1:nz, j=1:m, i=1:n)
      h(i,j,k) = h(i-1,j,k) + flux(i,j,k)
    end do
  end subroutine stencil_written

  ! REFUSAL: a plain (non-component) array indexed by a subset of the loop
  ! indices — the subset rule is for intent(in) component arrays only.
  subroutine subset_plain_array(h, dt2d, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(inout) :: h(n, m, nz)
    real(8), intent(in) :: dt2d(n, m)
    integer :: i, j, k
    do concurrent (k=1:nz, j=1:m, i=1:n)
      h(i,j,k) = h(i,j,k) * dt2d(i,j)
    end do
  end subroutine subset_plain_array

  ! Supported neighbor: a local ASSIGNED in the nest stays a per-iteration
  ! `let` (only a local the nest never writes becomes an input).
  subroutine local_written(h, flux, dt, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(inout) :: h(n, m, nz)
    real(8), intent(in) :: flux(n, m, nz)
    real(8), intent(in) :: dt
    real(8) :: w
    integer :: i, j, k
    do concurrent (k=1:nz, j=1:m, i=1:n)
      w = dt * flux(i,j,k)
      h(i,j,k) = h(i,j,k) + w
    end do
  end subroutine local_written

end module test_kernel_stencil
