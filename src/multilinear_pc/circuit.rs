/// circuit to verify poly commitment
use ark_ec::{pairing::{Pairing, self}, CurveGroup};
use digest::crypto_common::Iv;
use crate::multilinear_pc::data_structures::{
    Commitment, Proof, VerifierKey,
};
use ark_std::error::Error;
use ark_ec::ScalarMul;
use ark_ff::PrimeField;
use ark_r1cs_std::{prelude::*, fields::fp::FpVar, groups::bls12::G1PreparedVar};
use ark_relations::{
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use crate::ark_std::UniformRand;
use ark_std::ops::Sub;
use ark_ec::VariableBaseMSM;
use ark_std::ops::Mul;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::BigInteger;
use ark_std::marker::PhantomData;
use ark_std::borrow::Borrow;
use ark_ec::AffineRepr;

/// data structures used by multilinear extension commitment scheme
struct PSTVerification<E, IV>
where
    E: Pairing,
    IV: PairingVar<E>,
{
    vk: VerifierKey<E>,
    commitment: Commitment<E>,
    point: Vec<E::ScalarField>,
    value: E::ScalarField,
    proof: Proof<E>,
    _iv: PhantomData<IV>,
}


impl<E, IV> Clone for PSTVerification<E, IV> 
    where
    E: Pairing,
    IV: PairingVar<E>,
{
    fn clone(&self) -> Self {
        Self {
            vk: self.vk.clone(),
            commitment: self.commitment.clone(),
            point: self.point.clone(),
            value: self.value.clone(),
            proof: self.proof.clone(),
            _iv: self._iv,
        }
    }
}


impl<E, IV> PSTVerification<E, IV>
where
    E: Pairing,
    IV: PairingVar<E>,
{
    #[allow(dead_code)]
    pub fn new(vk: VerifierKey<E>, commitment: Commitment<E>, point: Vec<E::ScalarField>, value: E::ScalarField, proof: Proof<E>) -> Self {

        Self {
            vk,
            commitment,
            point,
            value,
            proof,
            _iv: PhantomData
        }
    }
}



impl<E, IV> ConstraintSynthesizer<<E as Pairing>::BaseField> for PSTVerification<E, IV>
where
    E: Pairing,
    IV: PairingVar<E>,
    IV::G1Var: CurveVar<E::G1, E::BaseField>,
    IV::G2Var: CurveVar<E::G2, E::BaseField>,
    IV::GTVar: FieldVar<E::TargetField, E::BaseField>,

{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<<E as Pairing>::BaseField>,
    ) -> Result<(), SynthesisError> {   
        
        // allocate verifierkey field
        let vk_g_var  = IV::G1Var::new_input(cs.clone(), || Ok(self.vk.g))?;

        
        let vk_h_var = IV::G2Var::new_input(cs.clone(), || Ok(self.vk.h))?;
        let mut vk_gmask_var = Vec::new();
        for g_mask in self.vk.g_mask_random.clone().into_iter(){
            let g_mask_var = IV::G1Var::new_input(cs.clone(), || Ok(g_mask))?;
            vk_gmask_var.push(g_mask_var);
        }

        // allocate commitment
        let com_g1_prod_var = IV::G1Var::new_input(cs.clone(), || Ok(self.commitment.g_product))?;


        // allocate point
        let mut point_var = Vec::new();
        for p in self.point.clone().into_iter(){
            let scalar_in_fq = &E::BaseField::from_bigint(<E::BaseField as PrimeField>::BigInt::from_bits_le(p.into_bigint().to_bits_le().as_slice())).unwrap();
            let p_var = FpVar::new_input(cs.clone(), || Ok(scalar_in_fq))?;
            point_var.push(p_var);
        }


        // allocate value
        let scalar_in_fq = &E::BaseField::from_bigint(<E::BaseField as PrimeField>::BigInt::from_bits_le(self.value.into_bigint().to_bits_le().as_slice())).unwrap();
        let value_var = FpVar::new_input(cs.clone(), || Ok(scalar_in_fq))?;


        // allocate proof
        let mut proofs_var = Vec::new();
        for proof in self.proof.proofs.clone().into_iter(){
            let proof_var = IV::G2Var::new_witness(cs.clone(), || Ok(proof))?;
            proofs_var.push(proof_var);
        }


        // start operation on circuit
        let pair_left_op = com_g1_prod_var - (vk_g_var.scalar_mul_le(value_var.to_bits_le()?.iter())?);
        let left_prepared = IV::prepare_g1(&pair_left_op)?;
        let right_prepared = IV::prepare_g2(&vk_h_var)?;
        let left = IV::pairing(left_prepared, right_prepared)?;
        

        //this section verify that the gmul calculated inside the circuit is equal to the gmul calculated with msm on native variable and then allocated as circuit variable
        // //calculating msm with framework function outside the circuit
        // let scalar_size = E::ScalarField::MODULUS_BIT_SIZE as usize;
        // let window_size = FixedBase::get_mul_window_size(self.vk.nv);

        /*
        let g_table = FixedBase::get_window_table(scalar_size, window_size, self.vk.g.into_group());
        let g_mul: Vec<E::G1> = FixedBase::msm(scalar_size, window_size, &g_table, self.point.as_slice());

        //calculate basic msm
        let mut res = Vec::new();
        for s in self.point.into_iter() {
            res.push(self.vk.g.mul(s));
        }
        
        //check basic msm with frameworks msm
        assert_eq!(res, g_mul);

        //do naive msm with circuit variable
        let mut g_mul_var = Vec::new();
        for g_m in g_mul.clone().into_iter(){
            let g_m_var = IV::G1Var::new_input(cs.clone(), || Ok(g_m))?;
            g_mul_var.push(g_m_var);
        }

        //assert vector calculated with msm and allocated is equal to msm calculated locally with variable
        res_var.enforce_equal(&g_mul_var)?;
        */  


        let mut g_mul_var: Vec<_> = Vec::new();
        for p in point_var.into_iter() {
            let x = vk_g_var.scalar_mul_le(p.to_bits_le()?.iter())?;
            g_mul_var.push(x);
        }


        let pairing_lefts_var: Vec<_> = (0..self.vk.nv)
            .map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())    //.map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
            .collect();

        let mut pairing_lefts_prep = Vec::new();
        for var in pairing_lefts_var.clone().into_iter(){
            pairing_lefts_prep.push(IV::prepare_g1(&var).unwrap());
        }

        let mut pairing_right_prep = Vec::new();
        for var in proofs_var.clone().into_iter(){
            pairing_right_prep.push(IV::prepare_g2(&var).unwrap());
        }

        let right_ml = IV::miller_loop(&pairing_lefts_prep,&pairing_right_prep)?;
        let right = IV::final_exponentiation(&right_ml).unwrap();
        left.enforce_equal(&right)?;

        //left.enforce_not_equal(&right)?;

        Ok(())
    }

}


#[cfg(test)]
mod tests {
    use crate::ark_std::UniformRand;
    use crate::multilinear_pc::data_structures::UniversalParams;
    use crate::multilinear_pc::{MultilinearPC, circuit};
    use ark_bls12_377::Bls12_377;
    use ark_bls12_377::g1::G1Projective;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension};
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    type E = Bls12_377;
    use ark_relations::r1cs::ConstraintSystem;
    use digest::KeyInit;
    type Fr = <E as Pairing>::ScalarField;
    type Fp = <E as Pairing>::BaseField;    //base field here
    use super::*;
    use ark_ec::bls12::Bls12;
    type IV = ark_bls12_377::constraints::PairingVar;
    use ark_groth16::Groth16;
    use crate::ark_std::rand::SeedableRng;
    use ark_bw6_761::BW6_761 as P;
    use ark_crypto_primitives::snark::SNARK;
    use rand_core::OsRng;
    use ark_ff::{ToConstraintField, Field};
    use ark_groth16::prepare_verifying_key;

    //basic test to verify circuit correctness
    fn test_polynomial<R: RngCore>(
        uni_params: &UniversalParams<E>,
        poly: &impl MultilinearExtension<Fr>,
        rng: &mut R,
    ) {
        let nv = poly.num_vars();
        assert_ne!(nv, 0);
        let (ck, vk) = MultilinearPC::<E>::trim(&uni_params, nv);
        let point: Vec<_> = (0..nv).map(|_| Fr::rand(rng)).collect();
        let com = MultilinearPC::commit(&ck, poly);
        let proof = MultilinearPC::open(&ck, poly, &point);

        let value = poly.evaluate(&point).unwrap();
        let result = MultilinearPC::check(&vk, &com, &point, value, &proof);
        let circuit = PSTVerification{
            vk: vk, 
            commitment: com, 
            point: point, 
            value: value, 
            proof: proof,
            _iv: PhantomData::<IV>,
        };
        let cs = ConstraintSystem::<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    //testing with variable allocation - theory notion
    fn test_groth<R: RngCore>(
        uni_params: &UniversalParams<E>,
        poly: &impl MultilinearExtension<Fr>,
        rng: &mut R,
    ) {
        let nv = poly.num_vars();
        assert_ne!(nv, 0);
        let (ck, vk) = MultilinearPC::<E>::trim(&uni_params, nv);
        let point: Vec<_> = (0..nv).map(|_| Fr::rand(rng)).collect();
        let com = MultilinearPC::commit(&ck, poly);
        let proof = MultilinearPC::open(&ck, poly, &point);
        let vkk = vk.clone();
        let value = poly.evaluate(&point).unwrap();
        let result = MultilinearPC::check(&vk, &com, &point, value, &proof);
        //assert!(result);
        let circuit = PSTVerification{
            vk: vk, 
            commitment: com, 
            point: point, 
            value: value, 
            proof: proof,
            _iv: PhantomData::<IV>,
        };

    
   
        let mut rng2 = rand_chacha::ChaChaRng::seed_from_u64(1776);
        let (pk, vk) = Groth16::<P>::circuit_specific_setup(circuit.clone(), &mut rng2).unwrap();

        let proof = Groth16::<P>::prove(&pk, circuit.clone(), &mut OsRng).unwrap();
        let params = Groth16::<P>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng2).unwrap();
        let pvk = prepare_verifying_key(&params.vk);

        
        //test on G1
       
        let z = Fp::ONE;
        let zz = Fp::ZERO;

        //assert!(Groth16::<P>::verify(&vk, &[*x, *y, z], &proof).unwrap()); SI
        //assert!(Groth16::<P>::verify(&vk, &[*y, *x, z], &proof).unwrap()); NO invertiti
        //assert!(Groth16::<P>::verify(&vk, &[*x, *y, zz], &proof).unwrap()); NO zero


        //test on G1
        //G1 element x and y are defined over a Fp field
        let comm_g_prod = circuit.commitment.g_product;
        let x_c = comm_g_prod.x().unwrap();
        let y_c = comm_g_prod.y().unwrap();
        //assert!(Groth16::<P>::verify(&vk, &[*x, *y, z, *x_c, *y_c, z], &proof).unwrap());  SI 



        // In a quadratic extension field Fp2 over a base field Fp, an element can be represented as  a+b⋅α, where a and b belong to Fp
        // and α is a root of an irreducible polynomial over Fp

        //On G2 x and y are defined over a Fp2 field as c=a+b⋅α, is possible to extract a and b that are element of Fp reducing them as follow:
        //  - a is the residue of the real part of c after reducing it modulo p.
        //  - b is the residue of the coefficient of the imaginary part (the element multiplied by α after reducing it modulo p.

        //test on G2
        let vk_h = circuit.vk.h;
        
        let x_c0 = vk_h.x().unwrap().c0;
        let x_c1 = vk_h.x().unwrap().c1;
        
        let y_c0 = vk_h.y().unwrap().c0;
        let y_c1 = vk_h.y().unwrap().c1;
        

        //The one element in Fp2 is represented as 1 + 0 * α,  because in a field, the multiplicative identity element is 1 and the additive identity is 0
        //In this case, the element 1 + 0 * α, is the equivalent of the multiplicative identity within the field extension Fp2.
        //For operations within the field extension Fp2 the element 1 + 0 * α would act as the multiplicative identity, similar to how 1 is the multiplicative identity over Fp.


        let ONE = Fp::ONE;
        let ZERO = Fp::ZERO;
    
        assert!(Groth16::<P>::verify(&vk, &[x_c0, x_c1, y_c0, y_c1, ONE, ZERO], &proof).unwrap());   
        
    }

    fn test_final_groth<R: RngCore>(
        uni_params: &UniversalParams<E>,
        poly: &impl MultilinearExtension<Fr>,
        rng: &mut R,
    ) {

        let nv = poly.num_vars();
        assert_ne!(nv, 0);
        let (ck, vk) = MultilinearPC::<E>::trim(&uni_params, nv);
        let point: Vec<_> = (0..nv).map(|_| Fr::rand(rng)).collect();
        let com = MultilinearPC::commit(&ck, poly);
        let proof = MultilinearPC::open(&ck, poly, &point);
        let vkk = vk.clone();
        let value = poly.evaluate(&point).unwrap();
        let result = MultilinearPC::check(&vk, &com, &point, value, &proof);

        let circuit = PSTVerification{
            vk: vk, 
            commitment: com, 
            point: point, 
            value: value, 
            proof: proof,
            _iv: PhantomData::<IV>,
        };

        //testing on Bls12-377 - Groth on BW6-761

        //zero and one on Fp of Bls12-377
        let fp_zero = Fp::ZERO;
        let fp_one = Fp::ONE;


        //vk input
        //vk_g as G1
        let vk_g = circuit.clone().vk.g;

        let vk_g_x = vk_g.x;
        let vk_g_y = vk_g.y;

        let pub_vk_g = vec![vk_g_x,vk_g_y,fp_one];

        //vk_h as G2
        let vk_h = circuit.vk.h;
        
        let vk_h_x_c0 = vk_h.x().unwrap().c0;
        let vk_h_x_c1 = vk_h.x().unwrap().c1;
        let vk_h_y_c0 = vk_h.y().unwrap().c0;
        let vk_h_y_c1 = vk_h.y().unwrap().c1;

        let pub_vk_h = vec![vk_h_x_c0,vk_h_x_c1,vk_h_y_c0,vk_h_y_c1,fp_one,fp_zero];

        //g_mask_random as [G1]
        let mut pub_g_mask = Vec::new();
        for g_mask in circuit.clone().vk.g_mask_random.into_iter() {
            let g_mask_x = g_mask.x;
            let g_mask_y = g_mask.y;

            pub_g_mask.push(g_mask_x);
            pub_g_mask.push(g_mask_y);
            pub_g_mask.push(fp_one);
        }


        //commitment input as G1
        let comm = circuit.clone().commitment.g_product;

        let comm_x = comm.x;
        let comm_y = comm.y;

        let pub_comm = vec![comm_x,comm_y,fp_one];


        //point input as [ScalarField]
        let mut pub_point = Vec::new();

        for p in circuit.clone().point.into_iter() {
            let p_pub = <Bls12<ark_bls12_377::Config> as Pairing>::BaseField::from_bigint(<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField as PrimeField>::BigInt::from_bits_le(
                p.into_bigint().to_bits_le().as_slice(),
            ))
            .unwrap();
            pub_point.push(p_pub);
        }


        //value input as ScalarField
        let pub_value = vec![
        <Bls12<ark_bls12_377::Config> as Pairing>::BaseField::from_bigint(<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField as PrimeField>::BigInt::from_bits_le(
            circuit.clone().value.into_bigint().to_bits_le().as_slice(),
        ))
        .unwrap()];


        //final input
        let public_input = [pub_vk_g,pub_vk_h,pub_g_mask,pub_comm,pub_point,pub_value].concat();
        

        //Groth proof & verify
        let mut rng2 = rand_chacha::ChaChaRng::seed_from_u64(1776);
        let (opk, ovk) = Groth16::<P>::circuit_specific_setup(circuit.clone(), &mut rng2).unwrap();
        let opvk = Groth16::<P>::process_vk(&ovk).unwrap();
        let oproof = Groth16::<P>::prove(&opk, circuit, &mut rng2).unwrap();
        assert!(Groth16::<P>::verify_proof(&opvk, &oproof, &public_input).unwrap()); 

    }

    #[test]
    fn setup_commit_verify_correct_polynomials() {
        let mut rng = test_rng();

        // normal polynomials
        let uni_params = MultilinearPC::setup(10, &mut rng);

        let poly1 = DenseMultilinearExtension::rand(8, &mut rng);
        test_polynomial(&uni_params, &poly1, &mut rng);

        //test_groth(&uni_params, &poly1, &mut rng);

        test_final_groth(&uni_params, &poly1, &mut rng);

        // let poly2 = SparseMultilinearExtension::rand_with_config(9, 1 << 5, &mut rng);
        // test_polynomial(&uni_params, &poly2, &mut rng);

        // // single-variate polynomials

        // let poly3 = DenseMultilinearExtension::rand(1, &mut rng);
        // test_polynomial(&uni_params, &poly3, &mut rng);

        // let poly4 = SparseMultilinearExtension::rand_with_config(1, 1 << 1, &mut rng);
        // test_polynomial(&uni_params, &poly4, &mut rng);
    }


}