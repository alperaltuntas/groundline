// Conformance fixture (C++ side): function-result kernels — a non-void point
// function whose return value is the kernel's single output, the C++ mirror
// of tests/f90/test_kernel_function (Fortran `result(name)`). Distilled from
// TIM's `ratio_max_point`. Supported: every control-flow path ends in exactly
// one tail `return e`. The refuse_* functions pin the neighboring shapes.
// The prelude mirrors amrex::Real / amrex::literals / amrex::Math so the
// fixture is self-contained (no includes; clang++ alone suffices).

using Real = double;
constexpr Real operator""_rt(long double v) { return static_cast<Real>(v); }
namespace Math {
inline Real abs(Real x) { return x < 0 ? -x : x; }
}

// Supported: a local, then an if/else whose branches each end in a return.
Real capped_ratio_point(Real const a, Real const b, Real const maxrat) noexcept
{
    Real const q = maxrat * b;
    if (Math::abs(a) > Math::abs(q)) {
        return maxrat;
    } else {
        return a / b;
    }
}

// An early return: a `return` that is not in tail position (a statement
// follows the if it sits in).
Real refuse_early_return(Real const a) noexcept
{
    if (a > 0.0_rt) {
        return a;
    }
    return -a;
}

// A tail `if` without `else`: the fall-through path returns nothing, so the
// result is unassigned on that path (refused by functionalize).
Real refuse_missing_else(Real const a) noexcept
{
    if (a > 0.0_rt) {
        return a;
    }
}

// Two output conventions at once: a Real& parameter AND a return value.
Real refuse_mixed_outputs(Real& x, Real const a) noexcept
{
    x = x + a;
    return a;
}

// A bare `return` in a void kernel.
void refuse_void_return(Real& x, Real const a) noexcept
{
    x = x + a;
    return;
}
