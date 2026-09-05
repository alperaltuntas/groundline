! Function-result kernels: a Fortran FUNCTION whose result variable is the
! kernel's single output (dump: `FunctionSubprogram` / `FunctionStmt` with a
! `Suffix` naming the result). Distilled from MOM_continuity_PPM's
! `ratio_max`. The supported shape is `result(name)` with the result assigned
! on every control-flow path; the neighbors below pin the refusals.
module test_kernel_function
  implicit none
contains

  ! Supported: pure function, result(ratio), a local, if/else assigning the
  ! result on both paths. Mirrors ratio_max's shape (one local added so the
  ! Let path is exercised alongside the result).
  pure function capped_ratio(a, b, maxrat) result(ratio)
    real(8), intent(in) :: a, b, maxrat
    real(8) :: ratio
    real(8) :: q
    q = maxrat * b
    if (abs(a) > abs(q)) then
      ratio = maxrat
    else
      ratio = a / b
    end if
  end function capped_ratio

  ! REFUSAL: no result clause — the function name itself is the result
  ! variable (a different declaration story; unsupported until a kernel needs it).
  function plain_result(a)
    real(8), intent(in) :: a
    real(8) :: plain_result
    plain_result = 2.0 * a
  end function plain_result

  ! REFUSAL: result type given by a type prefix (dump: `PrefixSpec ->
  ! DeclarationTypeSpec`) — the result is then not declared in the
  ! specification part, and a prefix carrying type information is refused
  ! rather than dropped.
  real(8) function typed_prefix(a) result(r)
    real(8), intent(in) :: a
    r = 2.0 * a
  end function typed_prefix

  ! REFUSAL (functionalize): the result is not assigned on every path — the
  ! fall-through path returns an undefined value.
  function partial_result(a) result(r)
    real(8), intent(in) :: a
    real(8) :: r
    if (a > 0.0) r = a
  end function partial_result

  ! REFUSAL (functionalize): the result is read before its first assignment.
  function reads_result(a) result(r)
    real(8), intent(in) :: a
    real(8) :: r
    r = r + a
  end function reads_result

  ! REFUSAL: a function with an intent(inout) dummy — two output conventions
  ! (a result AND a mutated argument) in one procedure.
  function mixed_outputs(a, x) result(r)
    real(8), intent(in) :: a
    real(8), intent(inout) :: x
    real(8) :: r
    x = x + a
    r = a
  end function mixed_outputs

end module test_kernel_function
