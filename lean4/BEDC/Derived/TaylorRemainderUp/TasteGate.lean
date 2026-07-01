import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

inductive TaylorRemainderUp : Type
  | carrier

namespace TaylorRemainderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TaylorRemainderCarrier [AskSetup] [PackageSetup]
    (D P W E Q S H C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  UnaryHistory D ∧ UnaryHistory P ∧ UnaryHistory W ∧ UnaryHistory E ∧
    UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory G ∧ UnaryHistory N ∧ Cont D P W ∧ Cont W E Q ∧
        Cont Q S H ∧ PkgSig bundle G pkg ∧ PkgSig bundle N pkg ∧ hsame N N

theorem TaylorRemainderCarrier_route_certificate [AskSetup] [PackageSetup]
    {D P W E Q S H C G N readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorRemainderCarrier D P W E Q S H C G N bundle pkg →
      Cont Q S readback →
        Cont readback N sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row D ∨ hsame row P ∨ hsame row W ∨ hsame row E ∨
                    hsame row Q ∨ hsame row S ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont D P W ∧ Cont W E Q ∧
                    Cont Q S readback ∧ Cont readback N sealRead ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readbackRoute sealRoute sealPkg
  have dUnary : UnaryHistory D := carrier.left
  have pUnary : UnaryHistory P := carrier.right.left
  have wUnary : UnaryHistory W := carrier.right.right.left
  have eUnary : UnaryHistory E := carrier.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have dpw : Cont D P W :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have weq : Cont W E Q :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed qUnary sUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary nUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row P ∨ hsame row W ∨ hsame row E ∨
              hsame row Q ∨ hsame row S ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D P W ∧ Cont W E Q ∧ Cont Q S readback ∧
              Cont readback N sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact ⟨source.right, dpw, weq, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, sealReadUnary⟩

end TaylorRemainderUp
end BEDC.Derived
