use ark_std::perf_trace::{TimerInfo, AtomicUsize, Ordering};
use ark_std::{start_timer, end_timer};
use ff::Field;
use group::Curve;
use std::time::Instant;
use std::{iter, env::var};
use std::ops::RangeTo;

mod generated;

use super::{
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    lookup, permutation, vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX,
    ChallengeY, Error, ProvingKey,
};
use crate::plonk::{CodeGenerationData, Expression};
use crate::plonk::lookup::prover::{evaluate, Constructed};
use crate::plonk::prover::generated::evaluate_hardcoded;
use crate::poly::Rotation;
use crate::poly::{
    commitment::Params,
    multiopen::{self, ProverQuery},
    Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial,
};
use crate::{
    arithmetic::{eval_polynomial, BaseExt, CurveAffine},
    plonk::Assigned,
};
use crate::{
    poly::batch_invert_assigned,
    transcript::{EncodedChallenge, TranscriptWrite},
};

/// Temp
#[allow(missing_debug_implementations)]
pub struct MeasurementInfo {
    /// Temp
    pub measure: bool,
    /// Temp
    pub time: /*TimerInfo*/Instant,
    /// Message
    pub message: String,
    /// Indent
    pub indent: usize,
}

/// TEMP
pub static NUM_INDENT: AtomicUsize = AtomicUsize::new(0);

/// Temp
pub fn start_measure(msg: String) -> MeasurementInfo {
    let measure: u32 = var("MEASURE")
    .expect("No MEASURE env var was provided")
    .parse()
    .expect("Cannot parse MEASURE env var as u32");

    let indent = NUM_INDENT.fetch_add(1, Ordering::Relaxed);

    if measure == 1/* || msg.starts_with("compressed_cosets")*/ {
        MeasurementInfo {
            measure: true,
            time: /*start_timer!(|| msg)*/Instant::now(),
            message: msg,
            indent,
        }
    } else {
        MeasurementInfo {
            measure: false,
            time: /*TimerInfo {
                msg: "".to_string(),
                time: Instant::now(),
            }*/Instant::now(),
            message: "".to_string(),
            indent,
        }
    }
}

/// Temp
pub fn stop_measure(info: MeasurementInfo) {
    NUM_INDENT.fetch_sub(1, Ordering::Relaxed);

    if info.measure {
        let final_time = Instant::now() - info.time;
        let secs = final_time.as_secs();
        let millis = final_time.subsec_millis();
        let micros = final_time.subsec_micros() % 1000;
        //let nanos = final_time.subsec_nanos() % 1000;
        /*let out = if secs != 0 {
            format!("{}.{:03}s", secs, millis)
        } else if millis > 0 {
            format!("{}.{:03}ms", millis, micros)
        } else {
            ""
        };*/

        //if secs > 0 || millis >= 1 {
            println!("{}{} ........ {}.{:03}{:03}s", "*".repeat(info.indent), info.message, secs, millis, micros);
        //}

        //end_timer!(info.time);
    }
}

/// Get env variable
pub fn env_value(key: &str, default: usize) -> usize {
    match var(key) {
        Ok(val) => val.parse().unwrap(),
        Err(_) => default,
    }
}

/// Temp
pub fn log_info(msg: String) {
    if env_value("INFO", 0) != 0 {
        println!("{}", msg);
    }
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptWrite<C, E>,
    ConcreteCircuit: Circuit<C::Scalar>,
>(
    params: &Params<C>,
    pk: &ProvingKey<C>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[C::Scalar]]],
    transcript: &mut T,
) -> Result<(), Error> {
    use ark_std::{end_timer, start_timer};

    for instance in instances.iter() {
        if instance.len() != pk.vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    // Hash verification key into transcript
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;
    let mut meta = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut meta);

    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    let generate_code = false;
    if generate_code {
        let mut code_data = CodeGenerationData {
            results: vec![],
            constants: vec![],
            rotations: vec![],
        };
        let mut post_code = "".to_string();

        //let mut value_update = "F::zero()".to_string();
        for gate in meta.gates.iter() {
            for poly in gate.polynomials().iter() {
                let value = poly.generate_code2(&mut code_data);
                // value_update = format!("({} * y + {})", value_update, value);
                post_code += &format!("*value = *value * y + {};\n", value)
            }
        }
        // post_code += &format!("*value = {};\n\n", value_update);

        // + (product_coset[r_0] * (permuted_input_coset[idx] + beta) * (permuted_table_coset[idx] + gamma)  * active_rows * Yn)
        //- (product_coset[idx] * VALUE * active_rows * Yn);
        // (product_coset[0] * VALUE[0] * active_rows[0] * Yn[0]) + (product_coset[1] * VALUE[1] * active_rows[1] * Yn[1])

        post_code += &format!("let active_rows = one - (l_last[idx] + l_blind[idx]);\n");
        for (n, lookup) in pk.vk.cs.lookups.iter().enumerate() {
            post_code += &format!("let product_coset = &product_cosets[{}].values;\n", n);
            post_code += &format!("let permuted_input_coset = &permuted_input_cosets[{}].values;\n", n);
            post_code += &format!("let permuted_table_coset = &permuted_table_cosets[{}].values;\n", n);
            post_code += &format!("let a_minus_s = permuted_input_coset[idx] - permuted_table_coset[idx];\n");

            // Input coset
            let mut compressed_input_coset = lookup.input_expressions[0].generate_code2(&mut code_data);
            for expr in lookup.input_expressions.iter().skip(1) {
                let expr_value = expr.generate_code2(&mut code_data);
                compressed_input_coset = code_data.reuse_code(format!("({} * theta + {})", compressed_input_coset, expr_value));
            }

            /*post_code += &format!("let mut compressed_input_coset = F::zero();\n");
            for expr in lookup.input_expressions.iter() {
                let value = expr.generate_code2(&mut code_data);
                post_code += &format!("compressed_input_coset = compressed_input_coset * theta + {};\n", value);
            }*/

            // table coset
            let mut compressed_table_coset = lookup.table_expressions[0].generate_code2(&mut code_data);
            for expr in lookup.table_expressions.iter().skip(1) {
                let expr_value = expr.generate_code2(&mut code_data);
                compressed_table_coset = code_data.reuse_code(format!("({} * theta + {})", compressed_table_coset, expr_value));
            }

            // l_0(X) * (1 - z(X)) = 0
            // Polynomial::one_minus(self.product_coset.clone()) * &pk.l0,
            let value = &format!("(one - product_coset[idx]) * l0[idx]");
            post_code += &format!("*value = *value * y + ({});\n", value);

            // l_last(X) * (z(X)^2 - z(X)) = 0
            // (self.product_coset.clone() * &self.product_coset - &self.product_coset) * &pk.l_last
            let value = &format!("(product_coset[idx] * product_coset[idx] - product_coset[idx]) * l_last[idx]");
            post_code += &format!("*value = *value * y + ({});\n", value);

            // (1 - (l_last(X) + l_blind(X))) * (
            //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            // ) = 0
            let next = code_data.add_rotation(&Rotation::next());
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            let left = format!("product_coset[{}] * (permuted_input_coset[idx] + beta) * (permuted_table_coset[idx] + gamma)", next);
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            let right_gamma = code_data.reuse_code(format!("({} + gamma)", compressed_table_coset));
            let right = format!("product_coset[idx] * ({} + beta) * {}", compressed_input_coset, right_gamma);
            let value = &format!("({} - {}) * active_rows", left, right);
            post_code += &format!("*value = *value * y + ({});\n", value);

            // l_0(X) * (a'(X) - s'(X)) = 0
            // (permuted.permuted_input_coset.clone() - &permuted.permuted_table_coset) * &pk.l0
            let value = &format!("a_minus_s * l0[idx]");
            post_code += &format!("*value = *value * y + ({});\n", value);

            // (1 - (l_last + l_blind)) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
            let prev = code_data.add_rotation(&Rotation::prev());
            let value = &format!("a_minus_s * (permuted_input_coset[idx] - permuted_input_coset[{}]) * active_rows", prev);
            post_code += &format!("*value = *value * y + ({});\n", value);
        }
        let code = code_data.get_code(post_code);
        println!("{}", code);
    }

    struct InstanceSingle<C: CurveAffine> {
        pub instance_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub instance_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub instance_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    }

    let start = start_timer!(|| "instance");
    let instance: Vec<InstanceSingle<C>> = instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<C>, Error> {
            let instance_values = instance
                .iter()
                .map(|values| {
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), params.n as usize);
                    if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
                        return Err(Error::InstanceTooLarge);
                    }
                    for (poly, value) in poly.iter_mut().zip(values.iter()) {
                        *poly = *value;
                    }
                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let instance_commitments_projective: Vec<_> = instance_values
                .iter()
                .map(|poly| params.commit_lagrange(poly))
                .collect();
            let mut instance_commitments =
                vec![C::identity(); instance_commitments_projective.len()];
            C::Curve::batch_normalize(&instance_commitments_projective, &mut instance_commitments);
            let instance_commitments = instance_commitments;
            drop(instance_commitments_projective);

            for commitment in &instance_commitments {
                transcript.common_point(*commitment)?;
            }

            let instance_polys: Vec<_> = instance_values
                .iter()
                .map(|poly| {
                    let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                    domain.lagrange_to_coeff(lagrange_vec)
                })
                .collect();

            let instance_cosets: Vec<_> = instance_polys
                .iter()
                .map(|poly| domain.coeff_to_extended(poly.clone()))
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
                instance_cosets,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    struct AdviceSingle<C: CurveAffine> {
        pub advice_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub advice_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub advice_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    }

    let start = start_timer!(|| "advice");
    let advice: Vec<AdviceSingle<C>> = circuits
        .iter()
        .zip(instances.iter())
        .map(|(circuit, instances)| -> Result<AdviceSingle<C>, Error> {
            struct WitnessCollection<'a, F: Field> {
                k: u32,
                pub advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
                instances: &'a [&'a [F]],
                usable_rows: RangeTo<usize>,
                _marker: std::marker::PhantomData<F>,
            }

            impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
                fn enter_region<NR, N>(&mut self, _: N)
                where
                    NR: Into<String>,
                    N: FnOnce() -> NR,
                {
                    // Do nothing; we don't care about regions in this context.
                }

                fn exit_region(&mut self) {
                    // Do nothing; we don't care about regions in this context.
                }

                fn enable_selector<A, AR>(
                    &mut self,
                    _: A,
                    _: &Selector,
                    _: usize,
                ) -> Result<(), Error>
                where
                    A: FnOnce() -> AR,
                    AR: Into<String>,
                {
                    // We only care about advice columns here

                    Ok(())
                }

                fn query_instance(
                    &self,
                    column: Column<Instance>,
                    row: usize,
                ) -> Result<Option<F>, Error> {
                    if !self.usable_rows.contains(&row) {
                        return Err(Error::not_enough_rows_available(self.k));
                    }

                    self.instances
                        .get(column.index())
                        .and_then(|column| column.get(row))
                        .map(|v| Some(*v))
                        .ok_or(Error::BoundsFailure)
                }

                fn assign_advice<V, VR, A, AR>(
                    &mut self,
                    _: A,
                    column: Column<Advice>,
                    row: usize,
                    to: V,
                ) -> Result<(), Error>
                where
                    V: FnOnce() -> Result<VR, Error>,
                    VR: Into<Assigned<F>>,
                    A: FnOnce() -> AR,
                    AR: Into<String>,
                {
                    if !self.usable_rows.contains(&row) {
                        return Err(Error::not_enough_rows_available(self.k));
                    }

                    *self
                        .advice
                        .get_mut(column.index())
                        .and_then(|v| v.get_mut(row))
                        .ok_or(Error::BoundsFailure)? = to()?.into();

                    Ok(())
                }

                fn assign_fixed<V, VR, A, AR>(
                    &mut self,
                    _: A,
                    _: Column<Fixed>,
                    _: usize,
                    _: V,
                ) -> Result<(), Error>
                where
                    V: FnOnce() -> Result<VR, Error>,
                    VR: Into<Assigned<F>>,
                    A: FnOnce() -> AR,
                    AR: Into<String>,
                {
                    // We only care about advice columns here

                    Ok(())
                }

                fn copy(
                    &mut self,
                    _: Column<Any>,
                    _: usize,
                    _: Column<Any>,
                    _: usize,
                ) -> Result<(), Error> {
                    // We only care about advice columns here

                    Ok(())
                }

                fn fill_from_row(
                    &mut self,
                    _: Column<Fixed>,
                    _: usize,
                    _: Option<Assigned<F>>,
                ) -> Result<(), Error> {
                    Ok(())
                }

                fn push_namespace<NR, N>(&mut self, _: N)
                where
                    NR: Into<String>,
                    N: FnOnce() -> NR,
                {
                    // Do nothing; we don't care about namespaces in this context.
                }

                fn pop_namespace(&mut self, _: Option<String>) {
                    // Do nothing; we don't care about namespaces in this context.
                }
            }

            let unusable_rows_start = params.n as usize - (meta.blinding_factors() + 1);

            let mut witness = WitnessCollection {
                k: params.k,
                advice: vec![domain.empty_lagrange_assigned(); meta.num_advice_columns],
                instances,
                // The prover will not be allowed to assign values to advice
                // cells that exist within inactive rows, which include some
                // number of blinding factors and an extra row for use in the
                // permutation argument.
                usable_rows: ..unusable_rows_start,
                _marker: std::marker::PhantomData,
            };

            // Synthesize the circuit to obtain the witness and other information.
            ConcreteCircuit::FloorPlanner::synthesize(
                &mut witness,
                circuit,
                config.clone(),
                meta.constants.clone(),
            )?;

            let mut advice = batch_invert_assigned(witness.advice);

            // Add blinding factors to advice columns
            for advice in &mut advice {
                for cell in &mut advice[unusable_rows_start..] {
                    *cell = C::Scalar::rand();
                }
            }

            // Compute commitments to advice column polynomials
            let advice_commitments_projective: Vec<_> = advice
                .iter()
                .map(|poly| params.commit_lagrange(poly))
                .collect();
            let mut advice_commitments = vec![C::identity(); advice_commitments_projective.len()];
            C::Curve::batch_normalize(&advice_commitments_projective, &mut advice_commitments);
            let advice_commitments = advice_commitments;
            drop(advice_commitments_projective);

            for commitment in &advice_commitments {
                transcript.write_point(*commitment)?;
            }

            let advice_polys: Vec<_> = advice
                .clone()
                .into_iter()
                .map(|poly| domain.lagrange_to_coeff(poly))
                .collect();

            let advice_cosets: Vec<_> = advice_polys
                .iter()
                .map(|poly| domain.coeff_to_extended(poly.clone()))
                .collect();

            Ok(AdviceSingle {
                advice_values: advice,
                advice_polys,
                advice_cosets,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    let start = start_timer!(|| format!("lookups commit_permuted {}", instance.len()));
    let lookups: Vec<Vec<lookup::prover::Permuted<C>>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| -> Result<Vec<_>, Error> {
            // Construct and commit to permuted values for each lookup
            let start = start_timer!(|| format!("lookups commit_permuted {}", pk.vk.cs.lookups.len()));
            let ret = pk.vk
                .cs
                .lookups
                .iter()
                .map(|lookup| {
                    lookup.commit_permuted(
                        pk,
                        params,
                        domain,
                        theta,
                        &advice.advice_values,
                        &pk.fixed_values,
                        &instance.instance_values,
                        transcript,
                    )
                })
                .collect();
            end_timer!(start);
            ret
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    // Commit to permutations.
    let start = start_timer!(|| "permutations");
    let permutations: Vec<permutation::prover::Committed<C>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| {
            pk.vk.cs.permutation.commit(
                params,
                pk,
                &pk.permutation,
                &advice.advice_values,
                &pk.fixed_values,
                &instance.instance_values,
                beta,
                gamma,
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    let start = start_timer!(|| format!("lookups commit_product ({})", lookups.len()));
    let lookups: Vec<Vec<lookup::prover::Committed<C>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            let start = start_timer!(|| format!("lookup commit_product ({})", lookups.len()));
            // Construct and commit to products for each lookup
            let res = lookups
                .into_iter()
                .map(|lookup| lookup.commit_product(pk, params, beta, gamma, transcript))
                .collect::<Result<Vec<_>, _>>();
            end_timer!(start);
            res
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    // Commit to the vanishing argument's random polynomial for blinding h(x_3)
    let start = start_timer!(|| "vanishing");
    let vanishing = vanishing::Argument::commit(params, domain, transcript)?;
    end_timer!(start);

    // Obtain challenge for keeping all separate gates linearly independent
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    let start = start_timer!(|| format!("temp memcopies"));
    let (product_cosets, (permuted_input_cosets, permuted_table_cosets)): (Vec<_>, (Vec<_>, Vec<_>)) = lookups[0]
        .iter()
        .map(|lookup| (&lookup.product_coset, (&lookup.permuted_input_coset, &lookup.permuted_table_coset)))
        .unzip();
    end_timer!(start);
    let start = start_timer!(|| format!("h(X) poly optimized ({})", lookups[0].len()));
    let h_poly = pk.vk.domain.lagrange_from_vec_ext(
        evaluate_hardcoded(
            domain.extended_len(),
            1 << (domain.extended_k - params.k),
            &pk.fixed_cosets,
            &advice[0].advice_cosets,
            &instance[0].instance_cosets,
            *y,
            *beta,
            *gamma,
            *theta,
            &pk.l0,
            &pk.l_blind,
            &pk.l_last,
            &product_cosets,
            &permuted_input_cosets,
            &permuted_table_cosets,
        )
    );
    end_timer!(start);

    // Evaluate the h(X) polynomial's constraint system expressions for the permutation constraints.
    let start = start_timer!(|| "h(X) permutations");
    let (permutations, permutation_expressions): (Vec<_>, Vec<_>) = permutations
        .into_iter()
        .zip(advice.iter())
        .zip(instance.iter())
        .map(|((permutation, advice), instance)| {
            permutation.construct(
                pk,
                &pk.vk.cs.permutation,
                &pk.permutation,
                &advice.advice_cosets,
                &pk.fixed_cosets,
                &instance.instance_cosets,
                beta,
                gamma,
            )
        })
        .unzip();
    end_timer!(start);

    let verify_optimizations = false;
    if verify_optimizations {
        let start = start_timer!(|| format!("lookups commit_permuted {}", instance.len()));
        let compressed_cosets: Vec<Vec<lookup::prover::PermutedCosets<C>>> = instance
            .iter()
            .zip(advice.iter())
            .map(|(instance, advice)| -> Result<Vec<_>, Error> {
                // Construct and commit to permuted values for each lookup
                let start = start_timer!(|| format!("lookups commit_permuted cosets {}", pk.vk.cs.lookups.len()));
                let ret = pk.vk
                    .cs
                    .lookups
                    .iter()
                    .map(|lookup| {
                        lookup.commit_permuted_coset(
                            pk,
                            params,
                            domain,
                            theta,
                            &advice.advice_cosets,
                            &pk.fixed_cosets,
                            &instance.instance_cosets,
                        )
                    })
                    .collect();
                end_timer!(start);
                ret
            })
            .collect::<Result<Vec<_>, _>>()?;
        end_timer!(start);

        let start = start_timer!(|| format!("h(X) lookups ({})", lookups.len()));
        let lookup_expressions: Vec<Vec<_>> = lookups
            .iter()
            .zip(compressed_cosets.into_iter())
            .map(|(lookups, compressed_cosets)| {
                let start = start_timer!(|| format!("h(X) lookups int ({})", lookups.len()));
                // Evaluate the h(X) polynomial's constraint system expressions for the lookup constraints, if any.
                let res = lookups
                    .iter()
                    .zip(compressed_cosets.into_iter())
                    .map(|(p, cc)| p.construct_expressions(pk, beta, gamma, cc))
                    .collect();
                end_timer!(start);
                res
            })
            .collect();
        end_timer!(start);

        //println!("advice.len: {}", advice.len());
        //println!("permutation_expressions.len: {}", permutation_expressions.len());
        //println!("lookup_expressions.len: {}", lookup_expressions.len());
        let expressions = advice
            .iter()
            .zip(instance.iter())
            .zip(permutation_expressions.into_iter())
            .zip(lookup_expressions.into_iter())
            .flat_map(
                |(((advice, instance), permutation_expressions), lookup_expressions)| {
                    iter::empty()
                        // Custom constraints
                        .chain(meta.gates.iter().flat_map(move |gate| {
                            gate.polynomials().iter().map(move |poly| {
                                pk.vk.domain.lagrange_from_vec_ext(
                                evaluate(
                                        &pk.vk.domain,
                                        &poly,
                                        domain.extended_len(),
                                        1 << (domain.extended_k - params.k),
                                        &pk.fixed_cosets,
                                        &advice.advice_cosets,
                                        &instance.instance_cosets,
                                    ),
                                )
                            })
                        }))
                        // Permutation constraints, if any.
                        .chain(permutation_expressions.into_iter())
                        // Lookup constraints, if any.
                        .chain(lookup_expressions.into_iter().flatten())
                },
            );

        let h_poly_b = expressions.fold(domain.empty_extended(), |h_poly, v| h_poly * *y + &v);
        for idx in 0..h_poly.values.len() {
            if h_poly.values[idx] != h_poly_b.values[idx] {
                println!("*Incorrect Value: {:?} , {:?}", h_poly.values[idx], h_poly_b.values[idx]);
            }
        }
    }

    // Construct the vanishing argument's h(X) commitments
    let start = start_timer!(|| "h(X) vanishing");
    let vanishing = vanishing.construct(params, domain, h_poly, transcript)?;
    end_timer!(start);

    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let xn = x.pow(&[params.n as u64, 0, 0, 0]);

    let lookups: Vec<Vec<Constructed<C>>> = lookups
        .into_iter()
        .map(|lookups| {
            // Evaluate the h(X) polynomial's constraint system expressions for the lookup constraints, if any.
            lookups
                .into_iter()
                .map(|p| p.construct())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // Compute and hash instance evals for each circuit instance
    let start = start_timer!(|| "instance evals");
    for instance in instance.iter() {
        // Evaluate polynomials at omega^i x
        let instance_evals: Vec<_> = meta
            .instance_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(
                    &instance.instance_polys[column.index()],
                    domain.rotate_omega(*x, at),
                )
            })
            .collect();

        // Hash each instance column evaluation
        for eval in instance_evals.iter() {
            transcript.write_scalar(*eval)?;
        }
    }
    end_timer!(start);

    // Compute and hash advice evals for each circuit instance
    let start = start_timer!(|| "hash evals");
    for advice in advice.iter() {
        // Evaluate polynomials at omega^i x
        let advice_evals: Vec<_> = meta
            .advice_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(
                    &advice.advice_polys[column.index()],
                    domain.rotate_omega(*x, at),
                )
            })
            .collect();

        // Hash each advice column evaluation
        for eval in advice_evals.iter() {
            transcript.write_scalar(*eval)?;
        }
    }
    end_timer!(start);

    // Compute and hash fixed evals (shared across all circuit instances)
    let start = start_timer!(|| "fixed evals");
    let fixed_evals: Vec<_> = meta
        .fixed_queries
        .iter()
        .map(|&(column, at)| {
            eval_polynomial(&pk.fixed_polys[column.index()], domain.rotate_omega(*x, at))
        })
        .collect();
    end_timer!(start);

    // Hash each fixed column evaluation
    for eval in fixed_evals.iter() {
        transcript.write_scalar(*eval)?;
    }

    let vanishing = vanishing.evaluate(x, xn, domain, transcript)?;

    // Evaluate common permutation data
    pk.permutation.evaluate(x, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let start = start_timer!(|| format!("eval permutations ({})", permutations.len()));
    let permutations: Vec<permutation::prover::Evaluated<C>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> { permutation.evaluate(pk, x, transcript) })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    // Evaluate the lookups, if any, at omega^i x.
    let start = start_timer!(|| format!("eval lookups ({})", lookups.len()));
    let lookups: Vec<Vec<lookup::prover::Evaluated<C>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            let start = start_timer!(|| format!("eval lookups int ({})", lookups.len()));
            let res = lookups
                .into_iter()
                .map(|p| p.evaluate(pk, x, transcript))
                .collect::<Result<Vec<_>, _>>();
            end_timer!(start);
            res
        })
        .collect::<Result<Vec<_>, _>>()?;
    end_timer!(start);

    let instances = instance
        .iter()
        .zip(advice.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .flat_map(|(((instance, advice), permutation), lookups)| {
            iter::empty()
                .chain(
                    pk.vk
                        .cs
                        .instance_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &instance.instance_polys[column.index()],
                        }),
                )
                .chain(
                    pk.vk
                        .cs
                        .advice_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &advice.advice_polys[column.index()],
                        }),
                )
                .chain(permutation.open(pk, x))
                .chain(lookups.iter().flat_map(move |p| p.open(pk, x)).into_iter())
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(*x, at),
                    poly: &pk.fixed_polys[column.index()],
                }),
        )
        .chain(pk.permutation.open(x))
        // We query the h(X) polynomial at x
        .chain(vanishing.open(x));

    let start = start_timer!(|| "create_proof");
    let proof = multiopen::create_proof(params, transcript, instances).map_err(|_| Error::Opening);
    end_timer!(start);

    proof
}