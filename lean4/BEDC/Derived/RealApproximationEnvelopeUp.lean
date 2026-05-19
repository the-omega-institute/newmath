import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealApproximationEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealApproximationEnvelopePacket [AskSetup] [PackageSetup]
    (tolerance window dyadic classifier «seal» transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory classifier ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont tolerance window dyadic ∧ Cont dyadic classifier «seal» ∧
          Cont «seal» transport routes ∧ PkgSig bundle provenance pkg

theorem RealApproximationEnvelopePacket_namecert_obligations [AskSetup] [PackageSetup]
    {tolerance window dyadic classifier «seal» transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApproximationEnvelopePacket tolerance window dyadic classifier «seal» transport routes
        provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          RealApproximationEnvelopePacket tolerance window dyadic classifier «seal» transport
              routes provenance name bundle pkg ∧
            (hsame row tolerance ∨ hsame row window ∨ hsame row dyadic ∨
              hsame row classifier ∨ hsame row «seal»))
        (fun _row : BHist =>
          Cont tolerance window dyadic ∧ Cont dyadic classifier «seal» ∧
            PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨toleranceUnary, windowUnary, dyadicUnary, classifierUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameUnary, toleranceWindowDyadic,
    dyadicClassifierSeal, _sealTransportRoutes, provenancePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro tolerance
          (And.intro packetWitness (Or.inl (hsame_refl tolerance)))
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
          | inl sameTolerance =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTolerance)
          | inr rest =>
              cases rest with
              | inl sameWindow =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameWindow))
              | inr rest =>
                  cases rest with
                  | inl sameDyadic =>
                      exact Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)))
                  | inr rest =>
                      cases rest with
                      | inl sameClassifier =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameClassifier))))
                      | inr sameSeal =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))))
    }
    pattern_sound := by
      intro _row _sourceData
      exact ⟨toleranceWindowDyadic, dyadicClassifierSeal, provenancePkg⟩
    ledger_sound := by
      intro row sourceData
      cases sourceData.right with
      | inl sameTolerance =>
          exact
            And.intro (unary_transport toleranceUnary (hsame_symm sameTolerance))
              provenancePkg
      | inr rest =>
          cases rest with
          | inl sameWindow =>
              exact
                And.intro (unary_transport windowUnary (hsame_symm sameWindow))
                  provenancePkg
          | inr rest =>
              cases rest with
              | inl sameDyadic =>
                  exact
                    And.intro (unary_transport dyadicUnary (hsame_symm sameDyadic))
                      provenancePkg
              | inr rest =>
                  cases rest with
                  | inl sameClassifier =>
                      exact
                        And.intro
                          (unary_transport classifierUnary (hsame_symm sameClassifier))
                          provenancePkg
                  | inr sameSeal =>
                      exact
                        And.intro (unary_transport sealUnary (hsame_symm sameSeal))
                          provenancePkg
  }

end BEDC.Derived.RealApproximationEnvelopeUp
