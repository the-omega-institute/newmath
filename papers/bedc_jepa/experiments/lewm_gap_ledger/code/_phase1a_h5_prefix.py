from __future__ import annotations

import argparse
import io
import os
import tarfile
from pathlib import Path

import zstandard as zstd
from huggingface_hub import HfFileSystem


class CountingReader(io.RawIOBase):
    def __init__(self, raw):
        self.raw = raw
        self.bytes_read = 0

    def readable(self) -> bool:
        return True

    def read(self, size=-1):
        data = self.raw.read(size)
        if data:
            self.bytes_read += len(data)
        return data

    def readinto(self, b):
        data = self.raw.read(len(b))
        if not data:
            return 0
        n = len(data)
        b[:n] = data
        self.bytes_read += n
        return n


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="_tworoom_prefix.h5")
    parser.add_argument("--mib", type=int, default=768)
    parser.add_argument("--block-mib", type=int, default=4)
    args = parser.parse_args()

    target_bytes = args.mib * 1024 * 1024
    out = Path(args.out)
    fs = HfFileSystem()
    path = "datasets/quentinll/lewm-tworooms/tworoom.tar.zst"
    print(f"open remote: {path}", flush=True)
    with fs.open(path, "rb", block_size=args.block_mib * 1024 * 1024) as f:
        counted = CountingReader(f)
        reader = zstd.ZstdDecompressor().stream_reader(counted)
        tar = tarfile.open(fileobj=reader, mode="r|")
        member = next(iter(tar))
        print(f"member: {member.name} size={member.size}", flush=True)
        source = tar.extractfile(member)
        if source is None:
            raise RuntimeError("tar member has no extractable file object")
        written = 0
        chunk_size = 8 * 1024 * 1024
        with out.open("wb") as dst:
            while written < min(target_bytes, member.size):
                chunk = source.read(min(chunk_size, target_bytes - written))
                if not chunk:
                    break
                dst.write(chunk)
                written += len(chunk)
                if written % (128 * 1024 * 1024) == 0:
                    print(
                        f"written_uncompressed_mib={written / (1024 * 1024):.0f} "
                        f"compressed_read_mib={counted.bytes_read / (1024 * 1024):.2f}",
                        flush=True,
                    )
            if member.size > written:
                dst.seek(member.size - 1)
                dst.write(b"\0")
        print(f"out={out.resolve()}", flush=True)
        print(f"h5_declared_size={member.size}", flush=True)
        print(f"prefix_uncompressed_bytes={written}", flush=True)
        print(f"prefix_uncompressed_mib={written / (1024 * 1024):.2f}", flush=True)
        print(f"compressed_bytes_read={counted.bytes_read}", flush=True)
        print(f"compressed_mib_read={counted.bytes_read / (1024 * 1024):.2f}", flush=True)
        try:
            alloc = os.path.getsize(out)
            print(f"sparse_logical_size={alloc}", flush=True)
        except OSError:
            pass


if __name__ == "__main__":
    main()
