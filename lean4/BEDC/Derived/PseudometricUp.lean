import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PseudometricCarrier [AskSetup] [PackageSetup]
    (point distance dyadic stream readback sealRow zeroRow transport replay localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory point ∧ UnaryHistory distance ∧ UnaryHistory dyadic ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
      UnaryHistory zeroRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory localName ∧ Cont stream readback dyadic ∧
          Cont dyadic sealRow zeroRow ∧ hsame localName zeroRow ∧
            PkgSig bundle localName pkg

theorem PseudometricCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              PseudometricCarrier point distance dyadic stream readback sealRow zeroRow
                transport replay localName bundle pkg)
          (fun row : BHist =>
            hsame row zeroRow ∧ Cont stream readback dyadic ∧
              Cont dyadic sealRow zeroRow)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory point ∧ UnaryHistory distance ∧ UnaryHistory dyadic ∧
          UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
            UnaryHistory zeroRow ∧ Cont stream readback dyadic ∧
              Cont dyadic sealRow zeroRow ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier
  have carrierSource :
      PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg := carrier
  obtain ⟨pointUnary, distanceUnary, dyadicUnary, streamUnary, readbackUnary,
    sealUnary, zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, localNameZero, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              PseudometricCarrier point distance dyadic stream readback sealRow zeroRow
                transport replay localName bundle pkg)
          (fun row : BHist =>
            hsame row zeroRow ∧ Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName
        ⟨hsame_refl localName, carrierSource⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨hsame_trans source.left localNameZero, streamReadbackDyadic, dyadicSealZero⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, localNamePkg⟩
  }
  exact
    ⟨cert, pointUnary, distanceUnary, dyadicUnary, streamUnary, readbackUnary, sealUnary,
      zeroUnary, streamReadbackDyadic, dyadicSealZero, localNamePkg⟩

theorem PseudometricCarrier_separated_completion_readback [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      completionRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg →
      Cont zeroRow transport completionRead →
        UnaryHistory completionRead ∧ Cont stream readback dyadic ∧
          Cont dyadic sealRow zeroRow ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle Pkg
  intro carrier zeroTransportCompletion
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  exact
    ⟨unary_cont_closed zeroUnary transportUnary zeroTransportCompletion,
      streamReadbackDyadic,
      dyadicSealZero,
      localNamePkg⟩

end BEDC.Derived.PseudometricUp
