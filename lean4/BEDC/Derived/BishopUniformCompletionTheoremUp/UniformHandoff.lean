import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopUniformCompletionTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopUniformCompletionTheoremCarrier [AskSetup] [PackageSetup]
    (uniformCarrier cauchyFilter streamWindow regseqReadback realSeal universalHandoff
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory uniformCarrier ∧ UnaryHistory cauchyFilter ∧ UnaryHistory streamWindow ∧
    UnaryHistory regseqReadback ∧ UnaryHistory realSeal ∧ UnaryHistory universalHandoff ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont uniformCarrier cauchyFilter streamWindow ∧
          Cont streamWindow regseqReadback realSeal ∧
            Cont realSeal universalHandoff replay ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BishopUniformCompletionTheoremUniformHandoff [AskSetup] [PackageSetup]
    {uniformCarrier cauchyFilter streamWindow regseqReadback realSeal universalHandoff
      transport replay provenance localName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopUniformCompletionTheoremCarrier uniformCarrier cauchyFilter streamWindow
        regseqReadback realSeal universalHandoff transport replay provenance localName
        bundle pkg →
      Cont realSeal universalHandoff handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row uniformCarrier ∨ hsame row cauchyFilter ∨
                  hsame row streamWindow ∨ hsame row regseqReadback ∨
                    hsame row realSeal ∨ hsame row universalHandoff ∨
                      hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont realSeal universalHandoff handoffRead ∧
                  PkgSig bundle handoffRead pkg)
              hsame ∧
            UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BishopUniformCompletionTheoremCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealUniversal handoffPkg
  obtain ⟨_uniformUnary, _filterUnary, _streamUnary, _regseqUnary, realSealUnary,
    universalUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _uniformFilterStream, _streamRegseqSeal, _sealUniversalReplay,
    _transportReplayProvenance, _provenancePkg, _localPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed realSealUnary universalUnary sealUniversal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row uniformCarrier ∨ hsame row cauchyFilter ∨ hsame row streamWindow ∨
              hsame row regseqReadback ∨ hsame row realSeal ∨
                hsame row universalHandoff ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont realSeal universalHandoff handoffRead ∧
              PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealUniversal, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.BishopUniformCompletionTheoremUp
