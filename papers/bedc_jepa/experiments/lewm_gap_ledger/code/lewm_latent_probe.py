"""Minimal swm-free latent probe for public LeWM checkpoints.

This script intentionally avoids stable_worldmodel and mujoco. It rebuilds the
LeWM modules from torch/transformers plus the local jepa.py and module.py files.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

import torch
from huggingface_hub import HfApi, hf_hub_download
from torch import nn
from transformers import ViTConfig, ViTModel

from jepa import JEPA
from module import ARPredictor, Embedder, MLP


DEFAULT_REPO = "quentinll/lewm-reacher"
DEFAULT_FILENAME = "weights.pt"


def format_size(num_bytes: int | None) -> str:
    if num_bytes is None:
        return "unknown"
    mib = num_bytes / (1024 * 1024)
    return f"{num_bytes} bytes ({mib:.2f} MiB)"


def list_repo_files(repo_id: str) -> None:
    info = HfApi().model_info(repo_id=repo_id, files_metadata=True)
    print(f"repo: {repo_id}")
    print("files:")
    for sibling in info.siblings:
        name = sibling.rfilename
        suffix = Path(name).suffix or "(none)"
        print(f"  {name}\tformat={suffix}\tsize={format_size(sibling.size)}")


def make_vit_encoder(image_size: int, patch_size: int, embed_dim: int) -> ViTModel:
    # stable_pretraining.backbone.utils.vit_hf(size="tiny", patch_size=14)
    # matches a ViT-tiny layout: D=192, depth=12, MLP=768, 3 attention heads.
    vit_config = ViTConfig(
        image_size=image_size,
        patch_size=patch_size,
        num_channels=3,
        hidden_size=embed_dim,
        num_hidden_layers=12,
        num_attention_heads=3,
        intermediate_size=4 * embed_dim,
        qkv_bias=True,
    )
    return ViTModel(vit_config, add_pooling_layer=False)


def build_model(config: dict) -> JEPA:
    embed_dim = int(config["predictor"]["input_dim"])
    image_size = int(config["encoder"]["image_size"])
    patch_size = int(config["encoder"]["patch_size"])

    encoder = make_vit_encoder(image_size, patch_size, embed_dim)
    predictor = ARPredictor(
        num_frames=int(config["predictor"]["num_frames"]),
        input_dim=embed_dim,
        hidden_dim=int(config["predictor"]["hidden_dim"]),
        output_dim=int(config["predictor"]["output_dim"]),
        depth=int(config["predictor"]["depth"]),
        heads=int(config["predictor"]["heads"]),
        mlp_dim=int(config["predictor"]["mlp_dim"]),
        dim_head=int(config["predictor"]["dim_head"]),
        dropout=float(config["predictor"]["dropout"]),
        emb_dropout=float(config["predictor"]["emb_dropout"]),
    )
    action_encoder = Embedder(
        input_dim=int(config["action_encoder"]["input_dim"]),
        emb_dim=int(config["action_encoder"]["emb_dim"]),
    )
    projector = MLP(
        input_dim=int(config["projector"]["input_dim"]),
        hidden_dim=int(config["projector"]["hidden_dim"]),
        output_dim=int(config["projector"]["output_dim"]),
        norm_fn=nn.BatchNorm1d,
    )
    pred_proj = MLP(
        input_dim=int(config["pred_proj"]["input_dim"]),
        hidden_dim=int(config["pred_proj"]["hidden_dim"]),
        output_dim=int(config["pred_proj"]["output_dim"]),
        norm_fn=nn.BatchNorm1d,
    )
    return JEPA(
        encoder=encoder,
        predictor=predictor,
        action_encoder=action_encoder,
        projector=projector,
        pred_proj=pred_proj,
    )


def load_checkpoint(model: JEPA, checkpoint_path: str) -> dict[str, torch.Tensor]:
    state_dict = torch.load(checkpoint_path, map_location="cpu", weights_only=True)
    if not isinstance(state_dict, dict):
        raise TypeError(f"Expected a state_dict dict, got {type(state_dict)!r}")
    missing, unexpected = model.load_state_dict(state_dict, strict=True)
    if missing or unexpected:
        raise RuntimeError(f"load_state_dict mismatch: missing={missing}, unexpected={unexpected}")
    return state_dict


def summarize_state_dict(state_dict: dict[str, torch.Tensor]) -> None:
    prefix_counts = Counter(key.split(".", 1)[0] for key in state_dict)
    print(f"state_dict keys: {len(state_dict)}")
    print(f"top-level prefixes: {dict(prefix_counts)}")
    print(f"encoder cls token: {tuple(state_dict['encoder.embeddings.cls_token'].shape)}")
    print(f"encoder pos embeddings: {tuple(state_dict['encoder.embeddings.position_embeddings'].shape)}")
    print(
        "patch projection: "
        f"{tuple(state_dict['encoder.embeddings.patch_embeddings.projection.weight'].shape)}"
    )
    print(f"predictor pos_embedding: {tuple(state_dict['predictor.pos_embedding'].shape)}")
    print(f"action patch_embed: {tuple(state_dict['action_encoder.patch_embed.weight'].shape)}")
    print(f"projector first layer: {tuple(state_dict['projector.net.0.weight'].shape)}")


def run_probe(model: JEPA, config: dict, device: torch.device) -> tuple[torch.Size, torch.Size, float]:
    image_size = int(config["encoder"]["image_size"])
    action_dim = int(config["action_encoder"]["input_dim"])
    history_size = int(config["predictor"]["num_frames"])

    torch.manual_seed(0)
    pixels = torch.rand(2, history_size, 3, image_size, image_size, device=device)
    actions = torch.randn(2, history_size, action_dim, device=device)

    with torch.inference_mode():
        output = model.encode({"pixels": pixels, "action": actions})
        emb = output["emb"]
        pred = model.predict(emb, output["act_emb"])

        base = pixels[:1, :1].clone()
        perturbed = (base * torch.tensor([1.15, 0.85, 1.05], device=device).view(1, 1, 3, 1, 1) + 0.03).clamp(0, 1)
        base_emb = model.encode({"pixels": base})["emb"]
        perturbed_emb = model.encode({"pixels": perturbed})["emb"]
        l2 = torch.linalg.vector_norm(base_emb - perturbed_emb, dim=-1).item()

    print(f"emb.shape: {tuple(emb.shape)}")
    print(f"pred.shape: {tuple(pred.shape)}")
    print(f"latent_dim: {emb.shape[-1]}")
    print(f"color_perturb_l2: {l2:.6f}")
    return emb.shape, pred.shape, l2


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=DEFAULT_REPO, help="HuggingFace model repo id")
    parser.add_argument("--filename", default=DEFAULT_FILENAME, help="checkpoint filename")
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    args = parser.parse_args()

    list_repo_files(args.repo)
    checkpoint_path = hf_hub_download(args.repo, args.filename, repo_type="model")
    config_path = hf_hub_download(args.repo, "config.json", repo_type="model")
    print(f"checkpoint_path: {checkpoint_path}")
    print(f"config_path: {config_path}")

    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)

    model = build_model(config)
    state_dict = load_checkpoint(model, checkpoint_path)
    summarize_state_dict(state_dict)

    device = torch.device(args.device)
    model.to(device).eval()
    print(f"device: {device}")
    run_probe(model, config, device)


if __name__ == "__main__":
    main()
