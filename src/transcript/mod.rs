use merlin::Transcript;
use rug::Integer;
use algebra_core::{
    curves::ProjectiveCurve,
    PrimeField,
    bytes::ToBytes,
};
use crate::utils::{integer_to_bytes, ConvertibleUnknownOrderGroup, bigint_to_bytes};
use rug::integer::Order;

pub mod root;
pub mod modeq;
pub mod range;

pub use root::TranscriptProtocolRoot;
pub use modeq::TranscriptProtocolModEq;
pub use range::TranscriptProtocolRange;

quick_error! {
    #[derive(Debug)]
    pub enum TranscriptChannelError {
        Incomplete {}
    }
}


pub trait TranscriptProtocolMembershipPrime<G: ConvertibleUnknownOrderGroup, P: ProjectiveCurve>:
    TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P> + TranscriptProtocolRange<P> {

}

pub trait TranscriptProtocolChallenge {
    fn challenge_scalar(&mut self, label: &'static [u8], length_in_bits: u16) -> Integer;
}

pub trait TranscriptProtocolInteger<G: ConvertibleUnknownOrderGroup> {
    fn append_integer_scalar(&mut self, label: &'static [u8], scalar: &Integer);
    fn append_integer_point(&mut self, label: &'static [u8], point: &G::Elem);
}

pub trait TranscriptProtocolCurve<P: ProjectiveCurve> {
    fn append_curve_scalar(&mut self, label: &'static [u8], scalar: &P::ScalarField);
    fn append_curve_point(&mut self, label: &'static [u8], point: &P);
}

impl<G: ConvertibleUnknownOrderGroup> TranscriptProtocolInteger<G> for Transcript {
    fn append_integer_scalar(&mut self, label: &'static [u8], scalar: &Integer) {
        self.append_message(label, &integer_to_bytes(scalar));
    }

    fn append_integer_point(&mut self, label: &'static [u8], point: &G::Elem) {
        self.append_message(label, &integer_to_bytes(&G::elem_to(point)));
    }
}

impl<P: ProjectiveCurve> TranscriptProtocolCurve<P> for Transcript {
    fn append_curve_scalar(&mut self, label: &'static [u8], scalar: &P::ScalarField) {
        self.append_message(label, &bigint_to_bytes::<P>(&scalar.into_repr()));
    }

    fn append_curve_point(&mut self, label: &'static [u8], point: &P) {
        let affine = point.into_affine();
        let mut bytes = vec![];
        //TODO(kobi): make this safer and just better serialization
        affine.write(&mut bytes).unwrap();
        self.append_message(label, &bytes);
    }
}

impl TranscriptProtocolChallenge for Transcript {
    fn challenge_scalar(&mut self, label: &'static [u8], length_in_bits: u16) -> Integer {
        let mut buf = vec![0u8; (length_in_bits/8) as usize];
        self.challenge_bytes(label, &mut buf);
        Integer::from_digits(&buf[..], Order::MsfBe)
    }
}
