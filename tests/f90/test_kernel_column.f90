! A COLUMN kernel, distilled from MOM_continuity_PPM's zonal_BT_mass_flux:
! pointized over the column indices (j, i), the body is a sequence of
! k-passes — a `do concurrent (k,j,i)` MAP calling a banked point primitive
! (two intent(out) actuals land in per-k arrays), then a plain `do k;j;i`
! FOLD accumulating a per-column total. Around them, the shapes the real
! routine carries: a timer call (declared ignorable in the manifest), integer
! locals that only feed loop bounds, a whole-array assignment initializing the
! per-column output, and an OBC-style block guarded by a flag the manifest
! assumes false (its body would refuse if modeled — it reads q(i-1,j,k)).
! The siblings pin the boundary of the fold model.
module test_kernel_column
  implicit none

  type :: grid_t
    real(8), allocatable :: dy(:,:), iarea(:,:)
  end type grid_t

  type :: cs_t
    logical :: vol_cfl
  end type cs_t

contains

  subroutine timer_start()
  end subroutine timer_start

  subroutine timer_end()
  end subroutine timer_end

  ! The banked point primitive (a per-point elemental subroutine).
  elemental subroutine flux_pt(u, h, h_p1, q, dq, dy, iarea, iarea_p1, dt, vol_cfl)
    real(8), intent(in) :: u, h, h_p1, dy, iarea, iarea_p1, dt
    logical, intent(in) :: vol_cfl
    real(8), intent(out) :: q, dq
    real(8) :: cfl
    if (vol_cfl) then ; cfl = u * dt * iarea ; else ; cfl = u * dt * iarea_p1 ; endif
    q = dy * u * (h + cfl * (h_p1 - h))
    dq = dy * h
  end subroutine flux_pt

  ! Supported: the column kernel (columns = j, i; assume specified_bc = false;
  ! ignore_calls = timer_start, timer_end).
  subroutine column_sum(u, h, qbt, dt, g, cs, n, m, nz, specified_bc)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(0:n, m, nz), h(0:n+1, m, nz)
    real(8), intent(out) :: qbt(0:n, m)
    real(8), intent(in) :: dt
    type(grid_t), intent(in) :: g
    type(cs_t), intent(in) :: cs
    logical, intent(in) :: specified_bc
    real(8) :: q(0:n, m, nz), dq(0:n, m, nz)
    integer :: i, j, k, ie
    call timer_start()
    ie = n
    qbt(:,:) = 0.0
    do concurrent (k=1:nz, j=1:m, i=0:ie)
      call flux_pt(u(i,j,k), h(i,j,k), h(i+1,j,k), q(i,j,k), dq(i,j,k), &
                   g%dy(i,j), g%iarea(i,j), g%iarea(i+1,j), dt, cs%vol_cfl)
      if (specified_bc) q(i,j,k) = q(i-1,j,k)
    end do
    do k = 1, nz ; do j = 1, m ; do i = 0, ie
      qbt(i,j) = qbt(i,j) + q(i,j,k)
    end do ; end do ; end do
    call timer_end()
  end subroutine column_sum

  ! REFUSAL: a per-k write that depends on the fold state — a scan.
  subroutine scan(u, w, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(out) :: w(n, m, nz)
    real(8) :: acc(n, m)
    integer :: i, j, k
    acc(:,:) = 0.0
    do k = 1, nz ; do j = 1, m ; do i = 1, n
      acc(i,j) = acc(i,j) + u(i,j,k)
      w(i,j,k) = acc(i,j)
    end do ; end do ; end do
  end subroutine scan

  ! REFUSAL: a read of a per-k array at an offset in k — a k-recurrence.
  subroutine k_recurrence(u, w, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(inout) :: w(n, m, 0:nz)
    integer :: i, j, k
    do k = 1, nz ; do j = 1, m ; do i = 1, n
      w(i,j,k) = w(i,j,k-1) + u(i,j,k)
    end do ; end do ; end do
  end subroutine k_recurrence

  ! REFUSAL: a call to a procedure that is neither banked nor declared ignorable.
  subroutine unbanked_call(u, s, n, m, nz)
    integer, intent(in) :: n, m, nz
    real(8), intent(in) :: u(n, m, nz)
    real(8), intent(out) :: s(n, m)
    integer :: i, j, k
    s(:,:) = 0.0
    do k = 1, nz ; do j = 1, m ; do i = 1, n
      call timer_start()
      s(i,j) = s(i,j) + u(i,j,k)
    end do ; end do ; end do
  end subroutine unbanked_call

end module test_kernel_column
