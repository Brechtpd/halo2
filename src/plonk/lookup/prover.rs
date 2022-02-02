use super::super::{
    circuit::Expression, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error,
    ProvingKey,
};
use super::Argument;
use crate::plonk::{start_measure, stop_measure, log_info, CodeGenerationData};
use crate::poly::Basis;
use crate::{
    arithmetic::{eval_polynomial, parallelize, BaseExt, CurveAffine, FieldExt},
    poly::{
        commitment::Params, multiopen::ProverQuery, Coeff, EvaluationDomain, ExtendedLagrangeCoeff,
        LagrangeCoeff, Polynomial, Rotation,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use group::{
    ff::{BatchInvert, Field},
    Curve,
};
use std::any::TypeId;
use std::convert::TryInto;
use std::num::ParseIntError;
use std::{
    collections::BTreeMap,
    iter,
    ops::{Mul, MulAssign},
};
use ark_std::{end_timer, start_timer};

#[derive(Clone,Debug)]
pub(in crate::plonk) struct Permuted<C: CurveAffine> {
    compressed_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    /// Temp
    pub permuted_input_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    compressed_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    /// Temp
    pub permuted_table_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
}

pub(in crate::plonk) struct PermutedCosets<C: CurveAffine> {
    /// Temp
    pub compressed_input_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    /// Temp
    pub compressed_table_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
}

#[derive(Clone,Debug)]
pub/*(in crate::plonk)*/ struct Committed<C: CurveAffine> {
    /// Temp
    pub permuted_input_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    /// Temp
    pub permuted_table_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    /// Temp
    pub permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    /// Temp
    pub permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    /// Temp
    pub product_poly: Polynomial<C::Scalar, Coeff>,
    /// Temp
    pub product_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
}

pub(in crate::plonk) struct Constructed<C: CurveAffine> {
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    product_poly: Polynomial<C::Scalar, Coeff>,
}

pub(in crate::plonk) struct Evaluated<C: CurveAffine> {
    constructed: Constructed<C>,
}

impl<F: FieldExt> Argument<F> {
    /// Given a Lookup with input expressions [A_0, A_1, ..., A_{m-1}] and table expressions
    /// [S_0, S_1, ..., S_{m-1}], this method
    /// - constructs A_compressed = \theta^{m-1} A_0 + theta^{m-2} A_1 + ... + \theta A_{m-2} + A_{m-1}
    ///   and S_compressed = \theta^{m-1} S_0 + theta^{m-2} S_1 + ... + \theta S_{m-2} + S_{m-1},
    /// - permutes A_compressed and S_compressed using permute_expression_pair() helper,
    ///   obtaining A' and S', and
    /// - constructs Permuted<C> struct using permuted_input_value = A', and
    ///   permuted_table_expression = S'.
    /// The Permuted<C> struct is used to update the Lookup, and is then returned.
    pub(in crate::plonk) fn commit_permuted<
        'a,
        C,
        E: EncodedChallenge<C>,
        T: TranscriptWrite<C, E>,
    >(
        &self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        theta: ChallengeTheta<C>,
        advice_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
        instance_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
        transcript: &mut T,
        verify: bool,
    ) -> Result<Permuted<C>, Error>
    where
        C: CurveAffine<ScalarExt = F>,
        C::Curve: Mul<F, Output = C::Curve> + MulAssign<F>,
    {
        let start_general = start_measure(format!("commit_permuted"), false);

        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<C::Scalar>]| {
            // Values of input expressions involved in the lookup
            /*let start = start_measure(format!("compressed_expression ({})", expressions.len()));
            let unpermuted_expressions: Vec<_> = expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec(
                        evaluate(
                                &pk.vk.domain,
                                &expression,
                            params.n as usize,
                            1,
                            fixed_values,
                             advice_values,
                              instance_values,
                              false,
                            ),
                        )
                })
                .collect();
            // Compressed version of expressions
            let compressed_expression = unpermuted_expressions
                .iter()
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * *theta + expression
                });
            stop_measure(start);*/

            let start = start_measure(format!("compressed_expression ({})", expressions.len()), false);
            let compressed_expression = expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec(
                        evaluate(
                            &pk.vk.domain,
                            &expression,
                            params.n as usize,
                            1,
                            fixed_values,
                            advice_values,
                            instance_values,
                        ),
                    )
                })
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * *theta + &expression
                });
            stop_measure(start);

            /*for i in 0..compressed_expression.values.len() {
                if compressed_expression.values[i] != compressed_expression_combined.values[i] {
                    println!("FAILFAILFAIL")
                }
            };*/

            /*let start = start_measure(format!("compressed_cosets A"));
            let unpermuted_cosets: Vec<_> = expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec_ext(
                    evaluate(
                            &pk.vk.domain,
                            &expression,
                            domain.extended_len(),
                            1 << (domain.extended_k - params.k),
                            fixed_cosets,
                            advice_cosets,
                            instance_cosets,
                            true,
                        ),
                    )
                })
                .collect();

            let compressed_coset = unpermuted_cosets
                .iter()
                .fold(domain.empty_extended(), |acc, coset| {
                    acc * *theta + coset
                });
            stop_measure(start);*/

            /*let start = start_measure(format!("compressed_coset ({})", expressions.len()));
            let compressed_coset  = expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec_ext(
                    evaluate(
                            &pk.vk.domain,
                            &expression,
                            domain.extended_len(),
                            1 << (domain.extended_k - params.k),
                            fixed_cosets,
                            advice_cosets,
                            instance_cosets,
                            false,
                            None,
                        ),
                    )
                })
                .fold(domain.empty_extended(), |acc, coset| {
                    acc * *theta + &coset
                });
            stop_measure(start);*/

            /*for i in 0..compressed_coset.values.len() {
                if compressed_coset.values[i] != compressed_coset_combined.values[i] {
                    println!("FAILFAILFAIL")
                }
            };*/

            /*(
                compressed_expression,
                compressed_coset,
            )*/
            compressed_expression
        };

        // Closure to construct commitment to vector of values
        let commit_values = |values: &Polynomial<C::Scalar, LagrangeCoeff>| {
            let poly = pk.vk.domain.lagrange_to_coeff(values.clone());
            let commitment = params.commit_lagrange(values).to_affine();
            (poly, commitment)
        };

        // Get values of input expressions involved in the lookup and compress them
        let start = start_measure(format!("compress inputs"), false);
        let compressed_input_expression = compress_expressions(&self.input_expressions);
        stop_measure(start);

        // Get values of table expressions involved in the lookup and compress them
        let start = start_measure(format!("compress tables"), false);
        let compressed_table_expression = compress_expressions(&self.table_expressions);
        stop_measure(start);

        // Permute compressed (InputExpression, TableExpression) pair
        let start = start_measure(format!("permute"), false);
        let (permuted_input_expression, permuted_table_expression) = permute_expression_pair::<C>(
            pk,
            params,
            domain,
            &compressed_input_expression,
            &compressed_table_expression,
        )?;
        stop_measure(start);

        // Commit to permuted input expression
        let start = start_measure(format!("commit inputs"), false);
        let (permuted_input_poly, permuted_input_commitment) =
            commit_values(&permuted_input_expression);
        stop_measure(start);

        // Commit to permuted table expression
        let start = start_measure(format!("commit tables"), false);
        let (permuted_table_poly, permuted_table_commitment) =
            commit_values(&permuted_table_expression);
        stop_measure(start);

        // Hash permuted input commitment
        transcript.write_point(permuted_input_commitment)?;

        // Hash permuted table commitment
        transcript.write_point(permuted_table_commitment)?;

        // TODO: remove
        let start = start_measure(format!("input coset"), false);
        let permuted_input_coset = if verify {pk.vk.domain.coeff_to_extended(permuted_input_poly.clone()) } else { pk.vk.domain.lagrange_from_vec_ext(vec![]) };
        stop_measure(start);
        let start = start_measure(format!("table coset"), false);
        let permuted_table_coset = if verify {pk.vk.domain.coeff_to_extended(permuted_table_poly.clone()) } else { pk.vk.domain.lagrange_from_vec_ext(vec![]) };
        stop_measure(start);

        stop_measure(start_general);

        Ok(Permuted {
            compressed_input_expression,
            permuted_input_expression,
            permuted_input_poly,
            permuted_input_coset,
            compressed_table_expression,
            permuted_table_expression,
            permuted_table_poly,
            permuted_table_coset,
        })
    }

    /// Given a Lookup with input expressions [A_0, A_1, ..., A_{m-1}] and table expressions
    /// [S_0, S_1, ..., S_{m-1}], this method
    /// - constructs A_compressed = \theta^{m-1} A_0 + theta^{m-2} A_1 + ... + \theta A_{m-2} + A_{m-1}
    ///   and S_compressed = \theta^{m-1} S_0 + theta^{m-2} S_1 + ... + \theta S_{m-2} + S_{m-1},
    /// - permutes A_compressed and S_compressed using permute_expression_pair() helper,
    ///   obtaining A' and S', and
    /// - constructs Permuted<C> struct using permuted_input_value = A', and
    ///   permuted_table_expression = S'.
    /// The Permuted<C> struct is used to update the Lookup, and is then returned.
    pub(in crate::plonk) fn commit_permuted_coset<
        'a,
        C,
    >(
        &self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        theta: ChallengeTheta<C>,
        advice_cosets: &'a [Polynomial<C::Scalar, ExtendedLagrangeCoeff>],
        fixed_cosets: &'a [Polynomial<C::Scalar, ExtendedLagrangeCoeff>],
        instance_cosets: &'a [Polynomial<C::Scalar, ExtendedLagrangeCoeff>],
    ) -> Result<PermutedCosets<C>, Error>
    where
        C: CurveAffine<ScalarExt = F>,
        C::Curve: Mul<F, Output = C::Curve> + MulAssign<F>,
    {
        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<C::Scalar>]| {
            expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec_ext(
                    evaluate(
                            &pk.vk.domain,
                            &expression,
                            domain.extended_len(),
                            1 << (domain.extended_k - params.k),
                            fixed_cosets,
                            advice_cosets,
                            instance_cosets,
                        ),
                    )
                })
                .fold(domain.empty_extended(), |acc, coset| {
                    acc * *theta + &coset
                })
        };

        // Get values of input expressions involved in the lookup and compress them
        let start = start_measure(format!("compress inputs coset"), false);
        let compressed_input_coset = compress_expressions(&self.input_expressions);
        stop_measure(start);

        // Get values of table expressions involved in the lookup and compress them
        let start = start_measure(format!("compress tables coset"), false);
        let compressed_table_coset = compress_expressions(&self.table_expressions);
        stop_measure(start);

        Ok(PermutedCosets {
            compressed_input_coset,
            compressed_table_coset,
        })
    }
}

impl<C: CurveAffine> Permuted<C> {
    /// Given a Lookup with input expressions, table expressions, and the permuted
    /// input expression and permuted table expression, this method constructs the
    /// grand product polynomial over the lookup. The grand product polynomial
    /// is used to populate the Product<C> struct. The Product<C> struct is
    /// added to the Lookup and finally returned by the method.
    pub(in crate::plonk) fn commit_product<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        transcript: &mut T,
        verify: bool,
    ) -> Result<Committed<C>, Error> {
        let start = start_measure(format!("commit_product({})", 0), false);
        let blinding_factors = pk.vk.cs.blinding_factors();
        // Goal is to compute the products of fractions
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where a_j(X) is the jth input expression in this lookup,
        // where a'(X) is the compression of the permuted input expressions,
        // s_j(X) is the jth table expression in this lookup,
        // s'(X) is the compression of the permuted table expressions,
        // and i is the ith row of the expression.
        let mut lookup_product = vec![C::Scalar::zero(); params.n as usize];
        // Denominator uses the permuted input expression and permuted table expression
        parallelize(&mut lookup_product, |lookup_product, start| {
            for ((lookup_product, permuted_input_value), permuted_table_value) in lookup_product
                .iter_mut()
                .zip(self.permuted_input_expression[start..].iter())
                .zip(self.permuted_table_expression[start..].iter())
            {
                *lookup_product = (*beta + permuted_input_value) * &(*gamma + permuted_table_value);
            }
        });

        // Batch invert to obtain the denominators for the lookup product
        // polynomials
        lookup_product.iter_mut().batch_invert();

        // Finish the computation of the entire fraction by computing the numerators
        // (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        // * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        parallelize(&mut lookup_product, |product, start| {
            for (i, product) in product.iter_mut().enumerate() {
                let i = i + start;

                *product *= &(self.compressed_input_expression.values[i] + &*beta);
                *product *= &(self.compressed_table_expression.values[i] + &*gamma);
            }
        });

        // The product vector is a vector of products of fractions of the form
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where there are m input expressions and m table expressions,
        // a_j(\omega^i) is the jth input expression in this lookup,
        // a'j(\omega^i) is the permuted input expression,
        // s_j(\omega^i) is the jth table expression in this lookup,
        // s'(\omega^i) is the permuted table expression,
        // and i is the ith row of the expression.

        // Compute the evaluations of the lookup product polynomial
        // over our domain, starting with z[0] = 1
        let z = iter::once(C::Scalar::one())
            .chain(lookup_product)
            .scan(C::Scalar::one(), |state, cur| {
                *state *= &cur;
                Some(*state)
            })
            // Take all rows including the "last" row which should
            // be a boolean (and ideally 1, else soundness is broken)
            .take(params.n as usize - blinding_factors)
            // Chain random blinding factors.
            .chain((0..blinding_factors).map(|_| C::Scalar::rand()))
            .collect::<Vec<_>>();
        assert_eq!(z.len(), params.n as usize);
        let z = pk.vk.domain.lagrange_from_vec(z);

        #[cfg(feature = "sanity-checks")]
        // This test works only with intermediate representations in this method.
        // It can be used for debugging purposes.
        {
            // While in Lagrange basis, check that product is correctly constructed
            let u = (params.n as usize) - (blinding_factors + 1);

            // l_0(X) * (1 - z(X)) = 0
            assert_eq!(z[0], C::Scalar::one());

            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            for i in 0..u {
                let mut left = z[i + 1];
                let permuted_input_value = &self.permuted_input_expression[i];

                let permuted_table_value = &self.permuted_table_expression[i];

                left *= &(*beta + permuted_input_value);
                left *= &(*gamma + permuted_table_value);

                let mut right = z[i];
                let mut input_term = self.compressed_input_expression.values[i];
                let mut table_term = self.compressed_table_expression.values[i];

                input_term += &(*beta);
                table_term += &(*gamma);
                right *= &(input_term * &table_term);

                assert_eq!(left, right);
            }

            // l_last(X) * (z(X)^2 - z(X)) = 0
            // Assertion will fail only when soundness is broken, in which
            // case this z[u] value will be zero. (bad!)
            assert_eq!(z[u], C::Scalar::one());
        }
        let product_commitment = params.commit_lagrange(&z).to_affine();

        // Hash product commitment
        transcript.write_point(product_commitment)?;

        let z = pk.vk.domain.lagrange_to_coeff(z);

        // TODO: remove
        let product_coset = if verify { pk.vk.domain.coeff_to_extended(z.clone()) } else { pk.vk.domain.lagrange_from_vec_ext(vec![]) };

        stop_measure(start);

        Ok(Committed::<C> {
            permuted_input_poly: self.permuted_input_poly,
            permuted_table_poly: self.permuted_table_poly,
            permuted_input_coset: self.permuted_input_coset,
            permuted_table_coset: self.permuted_table_coset,
            product_poly: z,
            product_coset,
        })
    }
}

impl<'a, C: CurveAffine> Committed<C> {

    /// Given a Lookup with input expressions, table expressions, permuted input
    /// expression, permuted table expression, and grand product polynomial, this
    /// method constructs constraints that must hold between these values.
    /// This method returns the constraints as a vector of polynomials in
    /// the extended evaluation domain.
    pub(in crate::plonk) fn construct_expressions(
        &self,
        pk: &'a ProvingKey<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        cosets: PermutedCosets<C>,
    ) -> impl Iterator<Item = Polynomial<C::Scalar, ExtendedLagrangeCoeff>> + 'a {
        let domain = &pk.vk.domain;

        let active_rows = Polynomial::one_minus(pk.l_last.clone() + &pk.l_blind);

        let expressions = iter::empty()
            // l_0(X) * (1 - z(X)) = 0
            .chain(Some(
                Polynomial::one_minus(self.product_coset.clone()) * &pk.l0,
            ))
            // l_last(X) * (z(X)^2 - z(X)) = 0
            .chain(Some(
                (self.product_coset.clone() * &self.product_coset - &self.product_coset)
                    * &pk.l_last,
            ))
            // (1 - (l_last(X) + l_blind(X))) * (
            //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            // ) = 0
            .chain({
                // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                let mut left = domain.rotate_extended(&self.product_coset, Rotation::next());
                parallelize(&mut left, |left, start| {
                    for ((left, permuted_input), permuted_table) in left
                        .iter_mut()
                        .zip(self.permuted_input_coset[start..].iter())
                        .zip(self.permuted_table_coset[start..].iter())
                    {
                        *left *= &(*permuted_input + &(*beta));
                        *left *= &(*permuted_table + &(*gamma));
                    }
                });

                //left *= &(permuted.permuted_input_coset + &(*beta));
                //left *= &(permuted.permuted_table_coset + &(*gamma));

                //  z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
                let mut right = self.product_coset.clone();
                parallelize(&mut right, |right, start| {
                    for (i, right) in right.iter_mut().enumerate() {
                        let i = i + start;

                        // Add \beta and \gamma offsets
                        *right *= &(cosets.compressed_input_coset[i] + &*beta);
                        *right *= &(cosets.compressed_table_coset[i] + &*gamma);
                    }
                });

                Some((left - &right) * &active_rows)
            })
            // Check that the first values in the permuted input expression and permuted
            // fixed expression are the same.
            // l_0(X) * (a'(X) - s'(X)) = 0
            .chain(Some(
                (self.permuted_input_coset.clone() - &self.permuted_table_coset) * &pk.l0,
            ))
            // Check that each value in the permuted lookup input expression is either
            // equal to the value above it, or the value at the same index in the
            // permuted table expression.
            // (1 - (l_last + l_blind)) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
            .chain(Some(
                (self.permuted_input_coset.clone() - &self.permuted_table_coset)
                    * &(domain.sub_extended(
                        self.permuted_input_coset.clone(),
                        &self.permuted_input_coset,
                        Rotation::prev(),
                    ))
                    * &active_rows,
            ))
            ;

        expressions
    }

    /// Given a Lookup with input expressions, table expressions, permuted input
    /// expression, permuted table expression, and grand product polynomial, this
    /// method constructs constraints that must hold between these values.
    /// This method returns the constraints as a vector of polynomials in
    /// the extended evaluation domain.
    pub(in crate::plonk) fn construct(
        self,
    ) -> Constructed<C> {
        Constructed {
            permuted_input_poly: self.permuted_input_poly,
            permuted_table_poly: self.permuted_table_poly,
            product_poly: self.product_poly,
        }
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        pk: &ProvingKey<C>,
        x: ChallengeX<C>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let domain = &pk.vk.domain;
        let x_inv = domain.rotate_omega(*x, Rotation::prev());
        let x_next = domain.rotate_omega(*x, Rotation::next());

        let product_eval = eval_polynomial(&self.product_poly, *x);
        let product_next_eval = eval_polynomial(&self.product_poly, x_next);
        let permuted_input_eval = eval_polynomial(&self.permuted_input_poly, *x);
        let permuted_input_inv_eval = eval_polynomial(&self.permuted_input_poly, x_inv);
        let permuted_table_eval = eval_polynomial(&self.permuted_table_poly, *x);

        // Hash each advice evaluation
        for eval in iter::empty()
            .chain(Some(product_eval))
            .chain(Some(product_next_eval))
            .chain(Some(permuted_input_eval))
            .chain(Some(permuted_input_inv_eval))
            .chain(Some(permuted_table_eval))
        {
            transcript.write_scalar(eval)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        pk: &'a ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        let x_inv = pk.vk.domain.rotate_omega(*x, Rotation::prev());
        let x_next = pk.vk.domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            // Open lookup product commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.product_poly,
            }))
            // Open lookup input commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_input_poly,
            }))
            // Open lookup table commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_table_poly,
            }))
            // Open lookup input commitments at x_inv
            .chain(Some(ProverQuery {
                point: x_inv,
                poly: &self.constructed.permuted_input_poly,
            }))
            // Open lookup product commitments at x_next
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.product_poly,
            }))
    }
}

type ExpressionPair<F> = (Polynomial<F, LagrangeCoeff>, Polynomial<F, LagrangeCoeff>);

/// Given a vector of input values A and a vector of table values S,
/// this method permutes A and S to produce A' and S', such that:
/// - like values in A' are vertically adjacent to each other; and
/// - the first row in a sequence of like values in A' is the row
///   that has the corresponding value in S'.
/// This method returns (A', S') if no errors are encountered.
fn permute_expression_pair<C: CurveAffine>(
    pk: &ProvingKey<C>,
    params: &Params<C>,
    domain: &EvaluationDomain<C::Scalar>,
    input_expression: &Polynomial<C::Scalar, LagrangeCoeff>,
    table_expression: &Polynomial<C::Scalar, LagrangeCoeff>,
) -> Result<ExpressionPair<C::Scalar>, Error> {
    let blinding_factors = pk.vk.cs.blinding_factors();
    let usable_rows = params.n as usize - (blinding_factors + 1);

    let mut permuted_input_expression: Vec<C::Scalar> = input_expression.to_vec();
    permuted_input_expression.truncate(usable_rows);

    // Sort input lookup expression values
    permuted_input_expression.sort();

    // A BTreeMap of each unique element in the table expression and its count
    let mut leftover_table_map: BTreeMap<C::Scalar, u32> = table_expression
        .iter()
        .take(usable_rows)
        .fold(BTreeMap::new(), |mut acc, coeff| {
            *acc.entry(*coeff).or_insert(0) += 1;
            acc
        });
    let mut permuted_table_coeffs = vec![C::Scalar::zero(); usable_rows];

    let mut repeated_input_rows = permuted_input_expression
        .iter()
        .zip(permuted_table_coeffs.iter_mut())
        .enumerate()
        .filter_map(|(row, (input_value, table_value))| {
            // If this is the first occurence of `input_value` in the input expression
            if row == 0 || *input_value != permuted_input_expression[row - 1] {
                *table_value = *input_value;
                // Remove one instance of input_value from leftover_table_map
                if let Some(count) = leftover_table_map.get_mut(input_value) {
                    assert!(*count > 0);
                    *count -= 1;
                    None
                } else {
                    // Return error if input_value not found
                    Some(Err(Error::ConstraintSystemFailure))
                }
            // If input value is repeated
            } else {
                Some(Ok(row))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Populate permuted table at unfilled rows with leftover table elements
    for (coeff, count) in leftover_table_map.iter() {
        for _ in 0..*count {
            permuted_table_coeffs[repeated_input_rows.pop().unwrap() as usize] = *coeff;
        }
    }
    assert!(repeated_input_rows.is_empty());

    permuted_input_expression.extend((0..(blinding_factors + 1)).map(|_| C::Scalar::rand()));
    permuted_table_coeffs.extend((0..(blinding_factors + 1)).map(|_| C::Scalar::rand()));
    assert_eq!(permuted_input_expression.len(), params.n as usize);
    assert_eq!(permuted_table_coeffs.len(), params.n as usize);

    #[cfg(feature = "sanity-checks")]
    {
        let mut last = None;
        for (a, b) in permuted_input_expression
            .iter()
            .zip(permuted_table_coeffs.iter())
            .take(usable_rows)
        {
            if *a != *b {
                assert_eq!(*a, last.unwrap());
            }
            last = Some(*a);
        }
    }

    Ok((
        domain.lagrange_from_vec(permuted_input_expression),
        domain.lagrange_from_vec(permuted_table_coeffs),
    ))
}

/// TEMP
pub static mut EVALUATE_TOTAL_TIME: usize = 0;

pub fn evaluate<F: FieldExt, B: Basis>(
    domain: &EvaluationDomain<F>,
    expression: &Expression<F>,
    size: usize,
    rot_scale: i32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
) -> Vec<F> {
    //let code = expression.generate_code();
    //log_info(format!("Expression: {}", expression.generate_code()));

    /*let start = start_timer!(|| format!("expression normal"));

    let res = if TypeId::of::<B>() == TypeId::of::<LagrangeCoeff>() {
            expression.evaluate(
            &|scalar| domain.constant_lagrange(scalar),
            &|_| panic!("virtual selectors are removed during optimization"),
            &|_, column_index, rotation| {
                let c: Polynomial<F, LagrangeCoeff> = fixed[column_index].clone().into();
                fixed[column_index].clone().into::<Polynomial<F, LagrangeCoeff>>().unwrap().rotate(rotation)
            },
            &|_, column_index, rotation| {
                advice[column_index].clone().rotate(rotation)
            },
            &|_, column_index, rotation| {
                instance[column_index].clone().rotate(rotation)
            },
            &|a| -a,
            &|a, b| a + &b,
            &|a, b| {
                let mut modified_a = vec![F::one(); size];
                parallelize(&mut modified_a, |modified_a, start| {
                    for ((modified_a, a), b) in modified_a
                        .iter_mut()
                        .zip(a[start..].iter())
                        .zip(b[start..].iter())
                    {
                        *modified_a *= *a * b;
                    }
                });
                domain.lagrange_from_vec(modified_a)
            },
            &|a, scalar| a * scalar,
        )
    } else {
        expression.evaluate(
            &|scalar| domain.constant_extended(scalar),
            &|_| panic!("virtual selectors are removed during optimization"),
            &|_, column_index, rotation| {
                domain
                    .rotate_extended(&fixed[column_index], rotation)
            },
            &|_, column_index, rotation| {
                domain
                    .rotate_extended(&advice[column_index], rotation)
            },
            &|_, column_index, rotation| {
                domain
                    .rotate_extended(&instance[column_index], rotation)
            },
            &|a| -a,
            &|a, b| a + &b,
            &|a, b| a * &b,
            &|a, scalar| a * scalar,
        );
    }
    end_timer!(start);*/

    let start = start_measure(format!("expression opt"), false);
    let mut values = vec![F::zero(); size];

    parallelize(&mut values, |values, start| {
        let isize = size as i32;
        for (i, value) in values.iter_mut().enumerate() {
            let idx = i + start;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|_, column_index, rotation| {
                    let new_rotation = rot_scale * rotation.0;
                    fixed[column_index].values[(((idx as i32) + new_rotation).rem_euclid(isize)) as usize]
                },
                &|_, column_index, rotation| {
                    let new_rotation = rot_scale * rotation.0;
                    advice[column_index].values[(((idx as i32) + new_rotation).rem_euclid(isize)) as usize]
                },
                &|_, column_index, rotation| {
                    let new_rotation = rot_scale * rotation.0;
                    instance[column_index].values[(((idx as i32) + new_rotation).rem_euclid(isize)) as usize]
                },
                &|a| -a,
                &|a, b| a + &b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            );
        }
    });
    let duration = stop_measure(start);

    #[allow(unsafe_code)]
    unsafe {
        EVALUATE_TOTAL_TIME += duration;
    }

    values
}