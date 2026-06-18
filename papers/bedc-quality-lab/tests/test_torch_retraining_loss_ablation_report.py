import json

from bedc_quality_lab.torch_bedc_jepa import run_torch_retraining_loss_ablation


def test_retraining_loss_ablation_packet_is_json_ready():
    packet = run_torch_retraining_loss_ablation(seeds=(109,), train_count=48, test_count=24, epochs=4)

    decoded = json.loads(json.dumps(packet, sort_keys=True))

    torch_environment = decoded["torch_environment"]
    assert "device" not in torch_environment
    assert isinstance(torch_environment["resolved_device"], str)
    assert torch_environment["resolved_device"] in {"cpu", "cuda", "mps"}
    assert torch_environment["device_resolution"]["resolved_device"] == torch_environment["resolved_device"]
    assert isinstance(torch_environment["device_resolution"]["backend_details"], dict)
