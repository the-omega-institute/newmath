import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZnormalPacket [AskSetup] [PackageSetup]
    (typed fuel terminal normal continuation transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
    UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
          Cont continuation transports routes ∧ PkgSig bundle name pkg ∧
            PkgSig bundle provenance pkg

theorem ZnormalPacket_sibling_normalword_handoff [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      UnaryHistory normal →
        Cont normal continuation handoff →
          UnaryHistory handoff ∧ hsame handoff (append normal continuation) ∧
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet normalUnary normalContinuationHandoff
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalUnary continuationUnary normalContinuationHandoff
  exact ⟨handoffUnary, normalContinuationHandoff, namePkg, provenancePkg⟩

theorem ZnormalPacket_namecert_obligations [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
              bundle pkg ∧
            (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation))
        (fun _row : BHist =>
          Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
            Cont continuation transports routes ∧ PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro typed
          (And.intro packetWitness (Or.inl (hsame_refl typed)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceData
        constructor
        · exact sourceData.left
        · cases sourceData.right with
          | inl sameTyped =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTyped)
          | inr rest =>
              cases rest with
              | inl sameFuel =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFuel))
              | inr rest =>
                  cases rest with
                  | inl sameTerminal =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal)))
                  | inr rest =>
                      cases rest with
                      | inl sameNormal =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameNormal))))
                      | inr sameContinuation =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (hsame_trans (hsame_symm sameRows)
                                    sameContinuation))))
    }
    pattern_sound := by
      intro _row _sourceData
      exact
        ⟨typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
          provenancePkg⟩
    ledger_sound := by
      intro row sourceData
      cases sourceData.right with
      | inl sameTyped =>
          exact And.intro (unary_transport typedUnary (hsame_symm sameTyped)) provenancePkg
      | inr rest =>
          cases rest with
          | inl sameFuel =>
              exact And.intro (unary_transport fuelUnary (hsame_symm sameFuel)) provenancePkg
          | inr rest =>
              cases rest with
              | inl sameTerminal =>
                  exact And.intro
                    (unary_transport terminalUnary (hsame_symm sameTerminal)) provenancePkg
              | inr rest =>
                  cases rest with
                  | inl sameNormal =>
                      exact And.intro
                        (unary_transport normalUnary (hsame_symm sameNormal)) provenancePkg
                  | inr sameContinuation =>
                      exact And.intro
                        (unary_transport continuationUnary (hsame_symm sameContinuation))
                        provenancePkg
  }

end BEDC.Derived.ZnormalUp
