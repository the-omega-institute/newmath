import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.PrecompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive PrecompactMetricUp : Type where
  | mk (X D N F R M H C G Q : BHist) : PrecompactMetricUp
  deriving DecidableEq

def precompactMetricFields : PrecompactMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrecompactMetricUp.mk X D N F R M H C G Q => [X, D, N, F, R, M, H, C, G, Q]

def precompactMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: precompactMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: precompactMetricEncodeBHist h

def precompactMetricToEventFlow : PrecompactMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (precompactMetricFields x).map precompactMetricEncodeBHist

private theorem PrecompactMetricNameCert_obligations_encode_display
    (h : BHist) :
    ∀ m, List.Mem m (precompactMetricEncodeBHist h) →
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      intro m hm
      cases hm
  | e0 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inl rfl
      | tail _ hmTail =>
          exact ih m hmTail
  | e1 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inr rfl
      | tail _ hmTail =>
          exact ih m hmTail

private theorem PrecompactMetricNameCert_obligations_flow_display
    (rows : List BHist) :
    ∀ w m, List.Mem w (rows.map precompactMetricEncodeBHist) → List.Mem m w →
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction rows with
  | nil =>
      intro w m hw _hm
      cases hw
  | cons h rows ih =>
      intro w m hw hm
      cases hw with
      | head =>
          exact PrecompactMetricNameCert_obligations_encode_display h m hm
      | tail _ hwTail =>
          exact ih w m hwTail hm

theorem PrecompactMetricNameCert_obligations (x : PrecompactMetricUp) :
    (∃ rows : List BHist, rows = precompactMetricFields x) ∧
      (∀ w m, List.Mem w (precompactMetricToEventFlow x) → List.Mem m w →
        m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨precompactMetricFields x, rfl⟩
  · intro w m hw hm
    exact PrecompactMetricNameCert_obligations_flow_display
      (precompactMetricFields x) w m hw hm

end BEDC.Derived.PrecompactMetricUp
