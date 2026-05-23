import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatednessModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatednessModulusCarrier [AskSetup] [PackageSetup]
    (request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory request ∧ UnaryHistory locatedInterval ∧ UnaryHistory rationalCells ∧
    UnaryHistory dyadicRows ∧ UnaryHistory streamWindow ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LocatednessModulusCarrier_window_transport [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead streamWindow windowRead →
          Cont windowRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory request ∧ UnaryHistory locatedInterval ∧ UnaryHistory cellRead ∧
                UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                  Cont request locatedInterval cellRead ∧
                    Cont cellRead streamWindow windowRead ∧
                      Cont windowRead realSeal sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier requestLocated cellWindow windowSeal sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, _dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cellUnary streamUnary cellWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary realSealUnary windowSeal
  exact
    ⟨requestUnary, locatedUnary, cellUnary, windowUnary, sealUnary, requestLocated,
      cellWindow, windowSeal, provenancePkg, sealPkg⟩

theorem LocatednessModulusRealSeal_nonescape [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead streamWindow windowRead →
          Cont windowRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row request ∨ hsame row locatedInterval ∨ hsame row streamWindow ∨
                      hsame row realSeal ∨ hsame row sealRead)
                  (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier requestLocated cellWindow windowSeal sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, _dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cellUnary streamUnary cellWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary realSealUnary windowSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∨ hsame row locatedInterval ∨ hsame row streamWindow ∨
              hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealPkg⟩
  }
  exact ⟨cert, realSealUnary, sealUnary, sealPkg⟩

theorem LocatednessModulusCarrier_real_seal_non_escape [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead streamWindow windowRead →
          Cont windowRead realSeal sealRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row request ∨ hsame row locatedInterval ∨
                        hsame row streamWindow ∨ hsame row realSeal ∨ hsame row sealRead)
                    (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sealRead ∧ PkgSig bundle provenance pkg := by
  intro carrier requestLocated cellWindow windowSeal provenancePkg sealPkg
  obtain ⟨cert, _realSealUnary, sealUnary, _sealPkg⟩ :=
    LocatednessModulusRealSeal_nonescape carrier requestLocated cellWindow windowSeal sealPkg
  exact ⟨cert, sealUnary, provenancePkg⟩

end BEDC.Derived.LocatednessModulusUp
