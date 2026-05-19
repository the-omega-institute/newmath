import BEDC.Derived.RealityConstrainedExplanationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedExplanationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedExplanationNamecertObligations [AskSetup] [PackageSetup]
    {observation model phenomenon signature descent residue failure transport route provenance
      localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont observation model signature →
      Cont signature descent route →
        Cont residue failure publicRead →
          PkgSig bundle localName pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row publicRead ∧
                    ∃ packet : RealityConstrainedExplanationUp,
                      packet =
                        RealityConstrainedExplanationUp.mk observation model phenomenon
                          signature descent residue failure transport route provenance localName)
                (fun row : BHist =>
                  Cont observation model signature ∧ Cont signature descent route ∧
                    Cont residue failure row)
                (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro observationModelSignature signatureDescentRoute residueFailurePublicRead
    _localNamePkg publicReadPkg
  exact {
    core := {
      carrier_inhabited := by
        exact
          Exists.intro publicRead
            ⟨hsame_refl publicRead,
              Exists.intro
                (RealityConstrainedExplanationUp.mk observation model phenomenon signature
                  descent residue failure transport route provenance localName)
                rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨observationModelSignature, signatureDescentRoute, residueFailurePublicRead⟩
    ledger_sound := by
      intro row source
      cases source.left
      exact ⟨hsame_refl publicRead, publicReadPkg⟩
  }

end BEDC.Derived.RealityConstrainedExplanationUp
