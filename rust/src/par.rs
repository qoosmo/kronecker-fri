//! Optional parallelism (feature `parallel`, with rayon). Without the feature every helper runs
//! the same computation serially; the results are identical in both cases, since the work is
//! split into independent pieces whose outputs do not depend on the split.

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Grain of the parallel loops (elements per task).
pub(crate) const GRAIN: usize = 1 << 12;

/// `(0..n).map(f).collect()`.
pub(crate) fn map_range<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync + Send) -> Vec<T> {
    #[cfg(feature = "parallel")]
    {
        (0..n).into_par_iter().with_min_len(GRAIN).map(f).collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        (0..n).map(f).collect()
    }
}

/// Fill `out` by chunks: `f(start, chunk)` writes `out[start .. start + chunk.len()]`.
/// Serially, one call on the whole slice.
pub(crate) fn fill_chunks<T: Send>(out: &mut [T], f: impl Fn(usize, &mut [T]) + Sync + Send) {
    #[cfg(feature = "parallel")]
    {
        out.par_chunks_mut(GRAIN)
            .enumerate()
            .for_each(|(c, chunk)| f(c * GRAIN, chunk));
    }
    #[cfg(not(feature = "parallel"))]
    {
        f(0, out)
    }
}

/// Apply `f` to consecutive pairs of chunks `(lo, hi)` of two slices of equal length, with the
/// starting index of the chunk.
pub(crate) fn zip_chunks<T: Send>(
    lo: &mut [T],
    hi: &mut [T],
    f: impl Fn(usize, &mut [T], &mut [T]) + Sync + Send,
) {
    #[cfg(feature = "parallel")]
    {
        lo.par_chunks_mut(GRAIN)
            .zip(hi.par_chunks_mut(GRAIN))
            .enumerate()
            .for_each(|(c, (a, b))| f(c * GRAIN, a, b));
    }
    #[cfg(not(feature = "parallel"))]
    {
        f(0, lo, hi)
    }
}

/// Apply `f` to every chunk of length `len` of `v` (independent blocks).
pub(crate) fn for_blocks<T: Send>(v: &mut [T], len: usize, f: impl Fn(&mut [T]) + Sync + Send) {
    #[cfg(feature = "parallel")]
    {
        v.par_chunks_exact_mut(len).for_each(f);
    }
    #[cfg(not(feature = "parallel"))]
    {
        v.chunks_exact_mut(len).for_each(f);
    }
}

/// `(0..n).map(|i| f(buf, i)).collect()` with a scratch buffer per task.
pub(crate) fn map_range_buf<T: Send>(
    n: usize,
    f: impl Fn(&mut Vec<u8>, usize) -> T + Sync + Send,
) -> Vec<T> {
    #[cfg(feature = "parallel")]
    {
        (0..n)
            .into_par_iter()
            .with_min_len(GRAIN)
            .map_init(|| Vec::with_capacity(64), |b, i| f(b, i))
            .collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        let mut b = Vec::with_capacity(64);
        (0..n).map(|i| f(&mut b, i)).collect()
    }
}
