import BEDC.Derived.RealDiagonalRegularitySealUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealDiagonalRegularitySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealDiagonalRegularitySealCarrier [AskSetup] [PackageSetup]
    (D R G W T H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory W ∧ UnaryHistory T ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

def RealDiagonalRegularitySealClassifier
    (D W T Q R E H C P N D' W' T' Q' R' E' H' C' P' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame D D' ∧ hsame W W' ∧ hsame T T' ∧ hsame Q Q' ∧ hsame R R' ∧
    hsame E E' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
      Cont D W T ∧ Cont T Q R ∧ Cont R E C

theorem RealDiagonalRegularitySealClassifier_route_payload
    {D W T Q R E H C P N D' W' T' Q' R' E' H' C' P' N' : BHist} :
    RealDiagonalRegularitySealClassifier D W T Q R E H C P N D' W' T' Q' R' E'
        H' C' P' N' ->
      hsame D D' ∧ hsame W W' ∧ hsame T T' ∧ hsame Q Q' ∧ hsame R R' ∧
        hsame E E' ∧ Cont D W T ∧ Cont T Q R ∧ Cont R E C := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classifier
  obtain ⟨sameD, sameW, sameT, sameQ, sameR, sameE, _sameH, _sameC, _sameP,
    _sameN, diagonalWindow, triangleDyadic, regularityReal⟩ := classifier
  exact
    ⟨sameD, sameW, sameT, sameQ, sameR, sameE, diagonalWindow, triangleDyadic,
      regularityReal⟩

theorem RealDiagonalRegularitySealCarrier_obligations [AskSetup] [PackageSetup]
    {D W T Q R E H _C P N publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory W -> UnaryHistory T -> UnaryHistory Q ->
      UnaryHistory R -> UnaryHistory E -> hsame H (append D W) -> Cont D W T ->
        Cont T Q R -> Cont R E publicRead -> PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨
                  hsame row R ∨ hsame row E ∨ hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ Cont D W T ∧ Cont T Q R ∧
                  Cont R E publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryD unaryW _unaryT unaryQ _unaryR unaryE _sameH diagonalWindow
    triangleDyadic regularityReal provenancePkg namePkg
  have unaryTriangle : UnaryHistory T :=
    unary_cont_closed unaryD unaryW diagonalWindow
  have unaryRegularity : UnaryHistory R :=
    unary_cont_closed unaryTriangle unaryQ triangleDyadic
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryRegularity unaryE regularityReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨
            hsame row E ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont D W T ∧ Cont T Q R ∧ Cont R E publicRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, diagonalWindow, triangleDyadic, regularityReal, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, unaryPublic⟩

theorem RealDiagonalRegularitySealCarrier_scoped_consumer_route [AskSetup] [PackageSetup]
    {D W T Q R E H C P N publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory W -> UnaryHistory T -> UnaryHistory Q ->
      UnaryHistory R -> UnaryHistory E -> hsame H (append D W) -> Cont D W T ->
        Cont T Q R -> Cont R E publicRead -> PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨
                  hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ hsame H (append D W) ∧ Cont D W T ∧
                  Cont T Q R ∧ Cont R E publicRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
              hsame ∧
              UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryD unaryW _unaryT unaryQ _unaryR unaryE sameH diagonalWindow triangleDyadic
    regularityReal provenancePkg namePkg
  have unaryTriangle : UnaryHistory T :=
    unary_cont_closed unaryD unaryW diagonalWindow
  have unaryRegularity : UnaryHistory R :=
    unary_cont_closed unaryTriangle unaryQ triangleDyadic
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryRegularity unaryE regularityReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ hsame H (append D W) ∧ Cont D W T ∧
            Cont T Q R ∧ Cont R E publicRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, sameH, diagonalWindow, triangleDyadic, regularityReal, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, unaryTriangle, unaryRegularity, unaryPublic⟩

theorem RealDiagonalRegularitySealCarrier_nonescape [AskSetup] [PackageSetup]
    {D R G W T H C P N consumerRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalRegularitySealCarrier D R G W T H C P N bundle pkg ->
      Cont C P consumerRead -> Cont P N nameRead -> PkgSig bundle N pkg ->
        UnaryHistory consumerRead ∧ UnaryHistory nameRead ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg ∧
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row R ∨ hsame row G ∨ hsame row W ∨
                  hsame row T ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont P N nameRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier consumerRoute nameRoute namePkg
  obtain ⟨_unaryD, _unaryR, _unaryG, _unaryW, _unaryT, _unaryH, unaryC, unaryP,
    unaryN, provenancePkg, _carrierNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryC unaryP consumerRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryP unaryN nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row R ∨ hsame row G ∨ hsame row W ∨ hsame row T ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont P N nameRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg, nameRoute⟩
  }
  exact ⟨consumerUnary, nameUnary, provenancePkg, namePkg, cert⟩

end BEDC.Derived.RealDiagonalRegularitySealUp
