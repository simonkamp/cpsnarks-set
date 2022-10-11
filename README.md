SNARKs for Set Membership over commitments
------------

**The library is not ready for production use!**

This repo implements simplified RSA-based protocols used in the [Veksel](https://eprint.iacr.org/2021/327) paper from the work [Zero-Knowledge Proofs for Set Membership:
Efficient, Succinct, Modular](https://eprint.iacr.org/2019/1255.pdf).
Most of the code is from this [repo](https://github.com/kobigurk/cpsnarks-set) by Kobi Gurkan. Important differences include: 
- _it implements a simplified set membership scheme_. This version is not secure on its own without an additional range proof (the latter is described in the [Veksel paper](https://eprint.iacr.org/2021/327) and [its full implementation](https://github.com/matteocam/veksel)).
- it uses a [wrapper around rug-integer](https://github.com/matteocam/rug-binserial) to compute accurate proof sizes.

## License

This code is licensed under either of the following licenses, at your discretion.

 * [Apache License Version 2.0](LICENSE-APACHE)
 * [MIT License](LICENSE-MIT)

Unless you explicitly state otherwise, any contribution that you submit to this library shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.




