from fractions import Fraction

from mirror_packet_cert import Cq, MirrorPacketCertificate, NEG_ONE, ONE, ZERO


def check_basic_pair():
    cert = MirrorPacketCertificate(Fraction(1, 7), Fraction(14), 1, (), Fraction(1))
    p = cert.polynomial()
    assert p.eval(cert.lambda_plus()) == ONE
    assert p.eval(cert.lambda_minus()) == NEG_ONE
    assert cert.selected_contribution() == Cq(Fraction(-2), Fraction(0))
    assert cert.margin() == Fraction(1)
    assert cert.verifies_negative()


def check_extra_points():
    extra = (Cq.of(0, 14), Cq.of(1, 15), Cq.of(-1, 13))
    cert = MirrorPacketCertificate(Fraction(2, 5), Fraction(14), 2, extra, Fraction(3))
    p = cert.polynomial()
    assert p.eval(cert.lambda_plus()) == ONE
    assert p.eval(cert.lambda_minus()) == NEG_ONE
    for z in extra:
        assert p.eval(z) == ZERO
    assert cert.selected_contribution() == Cq(Fraction(-4), Fraction(0))
    assert cert.margin() == Fraction(1)
    assert cert.verifies_negative()


def check_boundary_case():
    cert = MirrorPacketCertificate(Fraction(1, 7), Fraction(14), 1, (), Fraction(2))
    assert cert.margin() == Fraction(0)
    assert not cert.verifies_negative()


if __name__ == "__main__":
    check_basic_pair()
    check_extra_points()
    check_boundary_case()
    print("ok")
