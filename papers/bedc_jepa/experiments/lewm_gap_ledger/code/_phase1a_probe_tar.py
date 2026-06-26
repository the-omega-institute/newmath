from __future__ import annotations

import io
import tarfile

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
    fs = HfFileSystem()
    path = "datasets/quentinll/lewm-tworooms/tworoom.tar.zst"
    print(f"opening {path}", flush=True)
    with fs.open(path, "rb") as f:
        counted = CountingReader(f)
        dctx = zstd.ZstdDecompressor()
        print("opening zstd stream", flush=True)
        with dctx.stream_reader(counted) as reader:
            print("opening tar stream", flush=True)
            with tarfile.open(fileobj=reader, mode="r|") as tar:
                print("iterating tar members", flush=True)
                for idx, member in enumerate(tar):
                    print(
                        f"{idx:03d}\tname={member.name}\tsize={member.size}\t"
                        f"type={'dir' if member.isdir() else 'file' if member.isfile() else member.type!r}",
                        flush=True,
                    )
                    if member.isfile() and member.size and idx < 8:
                        ext = member.name.rsplit(".", 1)[-1].lower() if "." in member.name else ""
                        if ext in {"json", "txt", "csv", "yaml", "yml"}:
                            fileobj = tar.extractfile(member)
                            if fileobj is not None:
                                sample = fileobj.read(min(member.size, 2048))
                                print("  sample:", sample[:512])
                    if idx >= 19:
                        break
        print(f"compressed_bytes_read={counted.bytes_read}")
        print(f"compressed_mib_read={counted.bytes_read / (1024 * 1024):.2f}")


if __name__ == "__main__":
    main()
