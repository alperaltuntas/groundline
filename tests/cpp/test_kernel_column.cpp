// Conformance fixture (C++ side): a COLUMN kernel — the mirror of
// tests/f90/test_kernel_column's `column_sum`, distilled from TIM's
// zonal_BT_mass_flux. The kernel is the body of a `ParallelFor` lambda over
// the horizontal cell (i, j): a per-column accumulator initialized to zero, a
// `for k` loop calling a banked point primitive with two `Real&` outputs
// received in uninitialized locals, a `+=` accumulation, and a per-column
// store `qbt(i,j,0)`. Reads `u(i,j,k)` are per-k arrays, `h(i+1,j,k)` a
// stencil, `dy(i,j,0)` a per-column scalar, `cs.vol_cfl` a member read on a
// const-reference struct parameter (a Bool input), and `specified_bc` a
// captured flag whose guarded block is pruned under the manifest hypothesis
// `specified_bc = false`. The prelude mirrors the AMReX shapes involved —
// `Array4::operator()`, `Box::smallEnd/bigEnd`, `ParallelFor(Box, lambda)` —
// so the fixture is self-contained (no includes; clang++ alone suffices).

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
}
using amrex::Box;
using amrex::Array4;
using amrex::ParallelFor;

struct cs_t { bool vol_cfl; };

// The banked point primitive the column kernel calls (two Real& outputs).
void flux_pt_point(Real const u, Real const h, Real const h_p1, Real& q, Real& dq,
                   Real const dy, Real const iarea, Real const iarea_p1, Real const dt,
                   bool const vol_cfl) noexcept
{
    Real cfl;
    if (vol_cfl) { cfl = u * dt * iarea; } else { cfl = u * dt * iarea_p1; }
    q = dy * u * (h + cfl * (h_p1 - h));
    dq = dy * h;
}

// Supported: the column kernel (ParallelFor #1 of this function).
void column_sum(const Box& bx, Array4<const Real> const& u, Array4<const Real> const& h,
                Array4<Real> const& qbt, Real dt, Array4<const Real> const& dy,
                Array4<const Real> const& iarea, const cs_t& cs, bool specified_bc)
{
    const int kmin = bx.smallEnd(2);
    const int kmax = bx.bigEnd(2);
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        Real qbt_val = 0.0_rt;
        for (int k = kmin; k <= kmax; ++k) {
            Real q_val, dq_val;
            flux_pt_point(u(i,j,k), h(i,j,k), h(i+1,j,k), q_val, dq_val,
                          dy(i,j,0), iarea(i,j,0), iarea(i+1,j,0), dt, cs.vol_cfl);
            if (specified_bc) { q_val = q_val / 2; }   // pruned: never modeled (an int literal would refuse)
            qbt_val += q_val;
        }
        qbt(i,j,0) = qbt_val;
    });
}

// REFUSAL: a per-k write that depends on the fold state — a scan.
void refuse_scan(const Box& bx, Array4<const Real> const& u, Array4<Real> const& w)
{
    const int kmin = bx.smallEnd(2);
    const int kmax = bx.bigEnd(2);
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        Real acc = 0.0_rt;
        for (int k = kmin; k <= kmax; ++k) {
            acc += u(i,j,k);
            w(i,j,k) = acc;
        }
    });
}

// REFUSAL: a call statement to a function that is not a banked primitive.
void helper(Real& acc, Real const x) noexcept { acc = acc + x; }
void refuse_unbanked_call(const Box& bx, Array4<const Real> const& u, Array4<Real> const& s)
{
    const int kmin = bx.smallEnd(2);
    const int kmax = bx.bigEnd(2);
    ParallelFor(bx, [=] (int i, int j, int) noexcept
    {
        Real acc = 0.0_rt;
        for (int k = kmin; k <= kmax; ++k) { helper(acc, u(i,j,k)); }
        s(i,j,0) = acc;
    });
}
