// Conformance fixture (C++ side): the mirror of tests/f90/test_kernel_bt_cont's
// `bt_cont`, distilled from TIM's set_zonal_BT_cont. Inside the `ParallelFor`
// lambda: a per-cell flag read `do_i(i,j,0) != 0` on an `Array4<const int>`
// (the integer array is readable only in this shape — it IS the Bool) bound
// to a `const bool` local; `const Real` PROLOGUE locals of the enclosing
// function (`idt`, `cfl_min`), captured by the lambda and hoisted into the
// model as the Fortran's pre-loop assignments are; `if (active) { … }` around
// two `for k` folds (the first with a conditional step, the second with two
// state variables and a call to the banked primitive) and a tail that writes
// three `Array4<Real>` outputs, with an `else` writing zeros; the same
// `if / else if` join reading both locals' prior values and the same
// re-assignment of `fa_0` after an output read it. Refusals: an integer
// Array4 read as a value (`!= 1`), and a non-const function-scope Real
// captured by the lambda. The prelude mirrors the AMReX shapes involved so
// the fixture is self-contained (clang++ alone suffices).

using Real = double;
constexpr Real operator""_rt(long double v) { return static_cast<Real>(v); }
namespace amrex {
struct Box {
    int lo[3]; int hi[3];
    int smallEnd(int d) const noexcept { return lo[d]; }
    int bigEnd(int d) const noexcept { return hi[d]; }
};
template <class T> struct Array4 {
    T* p; long jstride; long kstride;
    T& operator()(int i, int j, int k) const noexcept { return p[i + j*jstride + k*kstride]; }
};
template <class F> void ParallelFor(const Box& bx, F&& f) noexcept {
    for (int k = bx.lo[2]; k <= bx.hi[2]; ++k)
        for (int j = bx.lo[1]; j <= bx.hi[1]; ++j)
            for (int i = bx.lo[0]; i <= bx.hi[0]; ++i) f(i, j, k);
}
template <class T> constexpr const T& max(const T& a, const T& b) noexcept { return a < b ? b : a; }
}
using amrex::Box;
using amrex::Array4;
using amrex::ParallelFor;

// The banked point primitive the column kernel calls (two Real& outputs).
void flux_pt_point(Real const u, Real const h, Real& q, Real& dq, Real const dt) noexcept
{
    q = u * h * dt;
    dq = h * dt;
}

// Supported: the column kernel (ParallelFor #1 of this function).
void bt_cont(const Box& bx, Array4<const Real> const& u, Array4<const Real> const& h,
             Array4<Real> const& fa_w, Array4<Real> const& fa_e, Array4<Real> const& ubt,
             Array4<const Real> const& du0, Real dt, Array4<const Real> const& dx,
             Array4<const int> const& do_i)
{
    const Real idt = 1.0_rt / dt;
    const Real cfl_min = 1.0e-6_rt;
    const int kmin = bx.smallEnd(2);
    const int kmax = bx.bigEnd(2);
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        const bool active = (do_i(i,j,0) != 0);
        Real dul = amrex::max(0.0_rt, du0(i,j,0) + (cfl_min * idt) * dx(i,j,0));
        Real fa_l = 0.0_rt, uh_l = 0.0_rt;
        if (active) {
            for (int k = kmin; k <= kmax; ++k) {
                if (u(i,j,k) + dul < 0.0_rt) { dul = -u(i,j,k); }
            }
            for (int k = kmin; k <= kmax; ++k) {
                Real const u_l = u(i,j,k) + dul;
                Real q_l, dq_l;
                flux_pt_point(u_l, h(i+1,j,k), q_l, dq_l, dt);
                fa_l += dq_l;
                uh_l += q_l;
            }
            Real fa_0 = fa_l, fa_avg = fa_l;
            if ((dul - du0(i,j,0)) != 0.0_rt) { fa_avg = uh_l / (dul - du0(i,j,0)); }
            if (fa_avg > fa_0) { fa_avg = fa_0; } else if (fa_avg < 0.5_rt * fa_0) { fa_0 = fa_avg; }
            fa_w(i,j,0) = fa_0;
            fa_0 = 0.0_rt;
            fa_e(i,j,0) = fa_avg - fa_0;
            ubt(i,j,0) = 1.5_rt * (dul - du0(i,j,0));
        } else {
            fa_w(i,j,0) = 0.0_rt; fa_e(i,j,0) = 0.0_rt; ubt(i,j,0) = 0.0_rt;
        }
    });
}

// REFUSAL: an integer Array4 read as a value (only the `!= 0` flag shape is admitted).
void refuse_flag_value(const Box& bx, Array4<const Real> const& u, Array4<Real> const& s,
                       Array4<const int> const& do_i)
{
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        if (do_i(i,j,0) != 1) { s(i,j,0) = u(i,j,0); }
    });
}

// REFUSAL: a non-const function-scope Real captured by the lambda.
void refuse_nonconst_capture(const Box& bx, Array4<const Real> const& u, Array4<Real> const& s, Real dt)
{
    Real idt = 1.0_rt / dt;
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        s(i,j,0) = idt * u(i,j,0);
    });
}
