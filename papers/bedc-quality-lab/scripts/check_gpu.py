"""验证 PyTorch 能否调用 RTX 4090,并做一次矩阵乘法基准。"""
import torch
import time


def main():
    print(f"PyTorch 版本      : {torch.__version__}")
    print(f"CUDA 是否可用     : {torch.cuda.is_available()}")
    print(f"编译时 CUDA 版本  : {torch.version.cuda}")
    print(f"cuDNN 版本        : {torch.backends.cudnn.version()}")

    if not torch.cuda.is_available():
        raise SystemExit("❌ CUDA 不可用,GPU 调用失败")

    n = torch.cuda.device_count()
    print(f"GPU 数量          : {n}")
    for i in range(n):
        p = torch.cuda.get_device_properties(i)
        print(f"  [{i}] {p.name} | 显存 {p.total_memory/1024**3:.1f} GB "
              f"| 算力 {p.major}.{p.minor} | SM {p.multi_processor_count}")

    dev = torch.device("cuda:0")

    # 正确性:GPU 计算结果与 CPU 对比
    a = torch.randn(1000, 1000)
    b = torch.randn(1000, 1000)
    cpu_res = a @ b
    gpu_res = (a.to(dev) @ b.to(dev)).cpu()
    assert torch.allclose(cpu_res, gpu_res, atol=1e-3), "GPU/CPU 结果不一致"
    print("\n✅ GPU 矩阵乘法结果与 CPU 一致")

    # 性能基准:大矩阵乘法 (FP32)
    size = 8192
    x = torch.randn(size, size, device=dev)
    y = torch.randn(size, size, device=dev)
    torch.cuda.synchronize()
    # 预热
    for _ in range(3):
        _ = x @ y
    torch.cuda.synchronize()

    iters = 20
    t0 = time.perf_counter()
    for _ in range(iters):
        _ = x @ y
    torch.cuda.synchronize()
    dt = (time.perf_counter() - t0) / iters

    flops = 2 * size**3            # 一次方阵乘法的浮点运算数
    tflops = flops / dt / 1e12
    print(f"\n📊 {size}x{size} FP32 矩阵乘法基准:")
    print(f"   单次耗时   : {dt*1000:.2f} ms")
    print(f"   算力       : {tflops:.1f} TFLOPS (FP32)")

    mem = torch.cuda.max_memory_allocated(dev) / 1024**3
    print(f"   峰值显存   : {mem:.2f} GB")
    print("\n🎉 RTX 4090 调用成功")


if __name__ == "__main__":
    main()
