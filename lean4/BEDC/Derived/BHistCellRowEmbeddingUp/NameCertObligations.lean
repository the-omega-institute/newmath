import BEDC.Derived.BHistCellRowEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BHistCellRowEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BHistCellRowEmbeddingCarrier [AskSetup] [PackageSetup]
    (source bitRow width orbitZero readback transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧
    UnaryHistory bitRow ∧
      UnaryHistory width ∧
        UnaryHistory orbitZero ∧
          UnaryHistory readback ∧
            UnaryHistory transports ∧
              UnaryHistory routes ∧
                UnaryHistory provenance ∧
                  UnaryHistory name ∧
                    Cont source bitRow width ∧
                      Cont orbitZero readback routes ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle name pkg

theorem BHistCellRowEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source bitRow width orbitZero readback transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BHistCellRowEmbeddingCarrier source bitRow width orbitZero readback transports routes
        provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BHistCellRowEmbeddingCarrier source bitRow width orbitZero readback transports
              routes provenance name bundle pkg ∧
            (hsame row source ∨ hsame row bitRow ∨ hsame row width ∨
              hsame row orbitZero ∨ hsame row readback ∨ hsame row transports ∨
              hsame row routes ∨ hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont source bitRow width ∧ Cont orbitZero readback routes ∧
            PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory SemanticNameCert
  intro carrier
  have carrierPacket := carrier
  obtain ⟨sourceUnary, bitRowUnary, widthUnary, orbitZeroUnary, readbackUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, sourceBitWidth,
    orbitReadRoutes, provenancePkg, namePkg⟩ := carrier
  let SourceSpec :=
    fun row : BHist =>
      BHistCellRowEmbeddingCarrier source bitRow width orbitZero readback transports
          routes provenance name bundle pkg ∧
        (hsame row source ∨ hsame row bitRow ∨ hsame row width ∨
          hsame row orbitZero ∨ hsame row readback ∨ hsame row transports ∨
          hsame row routes ∨ hsame row provenance ∨ hsame row name)
  have sourceWitness : SourceSpec source := by
    exact ⟨carrierPacket, Or.inl (hsame_refl source)⟩
  have rowUnary :
      ∀ {row : BHist},
        (hsame row source ∨ hsame row bitRow ∨ hsame row width ∨
          hsame row orbitZero ∨ hsame row readback ∨ hsame row transports ∨
          hsame row routes ∨ hsame row provenance ∨ hsame row name) →
          UnaryHistory row := by
    intro row rowMember
    cases rowMember with
    | inl sameSource =>
        exact unary_transport sourceUnary (hsame_symm sameSource)
    | inr rest =>
        cases rest with
        | inl sameBitRow =>
            exact unary_transport bitRowUnary (hsame_symm sameBitRow)
        | inr rest =>
            cases rest with
            | inl sameWidth =>
                exact unary_transport widthUnary (hsame_symm sameWidth)
            | inr rest =>
                cases rest with
                | inl sameOrbitZero =>
                    exact unary_transport orbitZeroUnary (hsame_symm sameOrbitZero)
                | inr rest =>
                    cases rest with
                    | inl sameReadback =>
                        exact unary_transport readbackUnary (hsame_symm sameReadback)
                    | inr rest =>
                        cases rest with
                        | inl sameTransports =>
                            exact unary_transport transportsUnary (hsame_symm sameTransports)
                        | inr rest =>
                            cases rest with
                            | inl sameRoutes =>
                                exact unary_transport routesUnary (hsame_symm sameRoutes)
                            | inr rest =>
                                cases rest with
                                | inl sameProvenance =>
                                    exact
                                      unary_transport provenanceUnary
                                        (hsame_symm sameProvenance)
                                | inr sameName =>
                                    exact unary_transport nameUnary (hsame_symm sameName)
  exact {
    core := {
      carrier_inhabited := Exists.intro source sourceWitness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sourceRow with
        | intro carrierRow rowMember =>
            cases rowMember with
            | inl sameSource =>
                exact ⟨carrierRow, Or.inl (hsame_trans (hsame_symm sameRows) sameSource)⟩
            | inr rest =>
                cases rest with
                | inl sameBitRow =>
                    exact
                      ⟨carrierRow, Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameBitRow))⟩
                | inr rest =>
                    cases rest with
                    | inl sameWidth =>
                        exact
                          ⟨carrierRow, Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameWidth)))⟩
                    | inr rest =>
                        cases rest with
                        | inl sameOrbitZero =>
                            exact
                              ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameOrbitZero))))⟩
                        | inr rest =>
                            cases rest with
                            | inl sameReadback =>
                                exact
                                  ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameReadback)))))⟩
                            | inr rest =>
                                cases rest with
                                | inl sameTransports =>
                                    exact
                                      ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            sameTransports))))))⟩
                                | inr rest =>
                                    cases rest with
                                    | inl sameRoutes =>
                                        exact
                                          ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameRoutes)))))))⟩
                                    | inr rest =>
                                        cases rest with
                                        | inl sameProvenance =>
                                            exact
                                              ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr
                                                (Or.inr (Or.inr (Or.inr (Or.inl
                                                  (hsame_trans (hsame_symm sameRows)
                                                    sameProvenance))))))))⟩
                                        | inr sameName =>
                                            exact
                                              ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr
                                                (Or.inr (Or.inr (Or.inr (Or.inr
                                                  (hsame_trans (hsame_symm sameRows)
                                                    sameName))))))))⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨sourceBitWidth, orbitReadRoutes, provenancePkg⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨rowUnary sourceRow.right, namePkg⟩
  }

theorem BHistCellRowEmbedding_nonescape [AskSetup] [PackageSetup]
    {source bitRow width orbitZero readback transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BHistCellRowEmbeddingCarrier source bitRow width orbitZero readback transports routes
        provenance name bundle pkg →
      UnaryHistory source ∧
        UnaryHistory bitRow ∧
          UnaryHistory width ∧
            UnaryHistory orbitZero ∧
              UnaryHistory readback ∧
                UnaryHistory transports ∧
                  UnaryHistory routes ∧
                    UnaryHistory provenance ∧
                      UnaryHistory name ∧
                        Cont source bitRow width ∧
                          Cont orbitZero readback routes ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle name pkg ∧
                                (∀ row : BHist,
                                  (hsame row source ∨ hsame row bitRow ∨
                                      hsame row width ∨ hsame row orbitZero ∨
                                        hsame row readback ∨ hsame row transports ∨
                                          hsame row routes ∨ hsame row provenance ∨
                                            hsame row name) →
                                    UnaryHistory row) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, bitRowUnary, widthUnary, orbitZeroUnary, readbackUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, sourceBitWidth,
    orbitReadRoutes, provenancePkg, namePkg⟩ := carrier
  refine
    ⟨sourceUnary, bitRowUnary, widthUnary, orbitZeroUnary, readbackUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, sourceBitWidth,
      orbitReadRoutes, provenancePkg, namePkg, ?_⟩
  intro row rowMember
  cases rowMember with
  | inl sameSource =>
      exact unary_transport sourceUnary (hsame_symm sameSource)
  | inr rest =>
      cases rest with
      | inl sameBitRow =>
          exact unary_transport bitRowUnary (hsame_symm sameBitRow)
      | inr rest =>
          cases rest with
          | inl sameWidth =>
              exact unary_transport widthUnary (hsame_symm sameWidth)
          | inr rest =>
              cases rest with
              | inl sameOrbitZero =>
                  exact unary_transport orbitZeroUnary (hsame_symm sameOrbitZero)
              | inr rest =>
                  cases rest with
                  | inl sameReadback =>
                      exact unary_transport readbackUnary (hsame_symm sameReadback)
                  | inr rest =>
                      cases rest with
                      | inl sameTransports =>
                          exact unary_transport transportsUnary (hsame_symm sameTransports)
                      | inr rest =>
                          cases rest with
                          | inl sameRoutes =>
                              exact unary_transport routesUnary (hsame_symm sameRoutes)
                          | inr rest =>
                              cases rest with
                              | inl sameProvenance =>
                                  exact unary_transport provenanceUnary (hsame_symm sameProvenance)
                              | inr sameName =>
                                  exact unary_transport nameUnary (hsame_symm sameName)

end BEDC.Derived.BHistCellRowEmbeddingUp
