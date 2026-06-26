from __future__ import annotations

import argparse
from pathlib import Path

import h5py
import hdf5plugin  # noqa: F401 - registers external HDF5 filters such as blosc
import numpy as np


def summarize_array(arr: np.ndarray) -> str:
    arr = np.asarray(arr)
    parts = [f"shape={arr.shape}", f"dtype={arr.dtype}"]
    if arr.size:
        if np.issubdtype(arr.dtype, np.number) or arr.dtype == np.bool_:
            finite = arr[np.isfinite(arr)] if np.issubdtype(arr.dtype, np.floating) else arr.reshape(-1)
            if finite.size:
                parts.append(f"min={finite.min()}")
                parts.append(f"max={finite.max()}")
                parts.append(f"mean={finite.mean():.6g}")
        else:
            flat = arr.reshape(-1)
            parts.append(f"sample={flat[:5]!r}")
    return " ".join(parts)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", default="_tworoom_prefix.h5")
    args = parser.parse_args()

    path = Path(args.path)
    print(f"path={path.resolve()}")
    with h5py.File(path, "r") as h5:
        print("root attrs:")
        for k, v in h5.attrs.items():
            print(f"  {k}: {v!r}")

        datasets: list[str] = []

        def visitor(name, obj):
            if isinstance(obj, h5py.Dataset):
                datasets.append(name)
                print(
                    f"DATASET {name}: shape={obj.shape} dtype={obj.dtype} "
                    f"chunks={obj.chunks} compression={obj.compression} shuffle={obj.shuffle} "
                    f"maxshape={obj.maxshape}"
                )
                if obj.attrs:
                    for ak, av in obj.attrs.items():
                        print(f"  attr {ak}: {av!r}")
            elif isinstance(obj, h5py.Group):
                print(f"GROUP {name}")
                if obj.attrs:
                    for ak, av in obj.attrs.items():
                        print(f"  attr {ak}: {av!r}")

        h5.visititems(visitor)

        print("\nfirst-row samples:")
        for name in datasets:
            ds = h5[name]
            try:
                if ds.shape == ():
                    arr = ds[()]
                else:
                    n = min(5, ds.shape[0])
                    arr = ds[:n]
                print(f"{name}: {summarize_array(arr)}")
            except Exception as e:
                print(f"{name}: READ_ERROR {type(e).__name__}: {e}")


if __name__ == "__main__":
    main()
