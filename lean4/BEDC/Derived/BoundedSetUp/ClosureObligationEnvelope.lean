import BEDC.Derived.BoundedSetUp.BallContainmentRoute
import BEDC.Derived.BoundedSetUp.RadiusLedger

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_closure_obligation_envelope [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead radiusRead
      envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont center radius radiusRead ->
            Cont ballRead replay envelopeRead ->
              PkgSig bundle envelopeRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
                        hsame row ball ∨ hsame row ballRead ∨ hsame row radiusRead ∨
                          hsame row envelopeRead ∨ Cont ballRead replay envelopeRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
                        PkgSig bundle envelopeRead pkg ∧ hsame row envelopeRead)
                    hsame ∧
                  UnaryHistory X ∧ UnaryHistory S ∧ UnaryHistory center ∧
                    UnaryHistory radius ∧ UnaryHistory ballRead ∧ UnaryHistory radiusRead ∧
                      UnaryHistory envelopeRead ∧ Cont S center memberRead ∧
                        Cont memberRead radius ballRead ∧ Cont center radius radiusRead ∧
                          Cont ballRead replay envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius centerRadius ballReplayEnvelope envelopePkg
  obtain ⟨xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusUnary centerRadius
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayEnvelope
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
              hsame row ball ∨ hsame row ballRead ∨ hsame row radiusRead ∨
                hsame row envelopeRead ∨ Cont ballRead replay envelopeRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
              PkgSig bundle envelopeRead pkg ∧ hsame row envelopeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro envelopeRead
        ⟨hsame_refl envelopeRead, envelopeUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, namePkg, envelopePkg, source.left⟩
  }
  exact
    ⟨cert, xUnary, sUnary, centerUnary, radiusUnary, ballReadUnary, radiusReadUnary,
      envelopeUnary, subsetCenter, memberRadius, centerRadius, ballReplayEnvelope⟩

end BEDC.Derived.BoundedSetUp
