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
use crate::arithmetic::parallelize;
use crate::multicore;
use crate::plonk::{CodeGenerationData, Expression, scalar_to_string};
use crate::plonk::lookup::prover::{evaluate, Constructed, EVALUATE_TOTAL_TIME};
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
pub fn get_time() -> Instant {
    Instant::now()
}

/// Temp
pub fn get_duration(start: Instant) -> usize {
    let final_time = Instant::now() - start;
    let secs = final_time.as_secs() as usize;
    let millis = final_time.subsec_millis() as usize;
    let micros = (final_time.subsec_micros() % 1000) as usize;
    secs * 1000000 + millis * 1000 + micros
}

/// Temp
pub fn log_measurement(indent: Option<usize>, msg: String, duration: usize) {
    let indent = indent.unwrap_or(0);
    println!("{}{} ........ {}s", "*".repeat(indent), msg, (duration as f32)/1000000.0);
}

/// Temp
pub fn start_measure(msg: String, always: bool) -> MeasurementInfo {
    let measure: u32 = var("MEASURE")
    .expect("No MEASURE env var was provided")
    .parse()
    .expect("Cannot parse MEASURE env var as u32");

    let indent = NUM_INDENT.fetch_add(1, Ordering::Relaxed);

    if always || measure == 1/* || msg.starts_with("compressed_cosets")*/ {
        MeasurementInfo {
            measure: true,
            time: get_time(),
            message: msg,
            indent,
        }
    } else {
        MeasurementInfo {
            measure: false,
            time: get_time(),
            message: "".to_string(),
            indent,
        }
    }
}

/// Temp
pub fn stop_measure(info: MeasurementInfo) -> usize {
    NUM_INDENT.fetch_sub(1, Ordering::Relaxed);
    let duration = get_duration(info.time);
    if info.measure {
        log_measurement(Some(info.indent), info.message, duration);
    }
    duration
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

use crate::poly::FFT_TOTAL_TIME;
use crate::arithmetic::MULTIEXP_TOTAL_TIME;

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

    #[allow(unsafe_code)]
    unsafe {
        FFT_TOTAL_TIME = 0;
        MULTIEXP_TOTAL_TIME = 0;
        EVALUATE_TOTAL_TIME = 0;
    }

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
    let verify = false;
    let single_pass = false;

    if generate_code {
        let mut code_data = CodeGenerationData {
            results: vec![],
            constants: vec![],
            rotations: vec![],
        };
        code_data.add_constant(&C::ScalarExt::zero());
        code_data.add_constant(&C::ScalarExt::one());
        let mut post_code = "let mut value = zero;\n".to_string();

        //let mut value_update = "F::zero()".to_string();
        for gate in meta.gates.iter() {
            for poly in gate.polynomials().iter() {
                let value = poly.generate_code2(&mut code_data);
                // value_update = format!("({} * y + {})", value_update, value);
                post_code += &format!("value = value * y + {};\n", value)
            }
        }
        // post_code += &format!("*value = {};\n\n", value_update);

        let rot_next = code_data.add_rotation(&Rotation::next());
        let rot_prev = code_data.add_rotation(&Rotation::prev());
        for (n, lookup) in pk.vk.cs.lookups.iter().enumerate() {
            /*for (j, expr) in lookup.input_expressions.iter().enumerate() {
                let code = expr.generate_code();
                println!("i{},{}: {}", n, j, code);
            }
            for (j, expr) in lookup.table_expressions.iter().enumerate() {
                let code = expr.generate_code();
                println!("t{},{}: {}", n, j, code);
            }*/

            let write_lc = |code_data: &mut CodeGenerationData<_>, parts: Vec<String>| {
                let mut lc = parts[0].clone();
                let mut num_skipped = 0;
                for part in parts.iter().skip(1) {
                    if part == "c_0" {
                        num_skipped += 1;
                    } else {
                        if num_skipped == 0 {
                            lc = code_data.reuse_code(format!("({}*theta+{})", lc, part));
                        } else {
                            lc = code_data.reuse_code(format!("({}*theta{}+{})", lc, num_skipped, part));
                        }
                        num_skipped = 0;
                    }
                }
                if num_skipped > 0 {
                    if num_skipped == 1 {
                        lc = code_data.reuse_code(format!("({}*theta)", lc));
                    } else {
                        lc = code_data.reuse_code(format!("({}*theta{})", lc, num_skipped));
                    }
                }
                lc
            };

            // Input coset
            let input_parts = lookup.input_expressions.iter().map(|expr| expr.generate_code2(&mut code_data)).collect();
            let compressed_input_coset = write_lc(&mut code_data, input_parts);

            // Input coset
            /*let mut compressed_input_coset = lookup.input_expressions[0].generate_code2(&mut code_data);
            for expr in lookup.input_expressions.iter().skip(1) {
                let expr_value = expr.generate_code2(&mut code_data);
                if expr_value == "c_0" {
                    compressed_input_coset = code_data.reuse_code(format!("({}*theta)", compressed_input_coset));
                } else {
                    compressed_input_coset = code_data.reuse_code(format!("({}*theta+{})", compressed_input_coset, expr_value));
                }
            }*/

            /*post_code += &format!("let mut compressed_input_coset = F::zero();\n");
            for expr in lookup.input_expressions.iter() {
                let value = expr.generate_code2(&mut code_data);
                post_code += &format!("compressed_input_coset = compressed_input_coset * theta + {};\n", value);
            }*/

            // table coset
            let table_parts = lookup.table_expressions.iter().map(|expr| expr.generate_code2(&mut code_data)).collect();
            let compressed_table_coset = write_lc(&mut code_data, table_parts);
            /*let mut compressed_table_coset = lookup.table_expressions[0].generate_code2(&mut code_data);
            for expr in lookup.table_expressions.iter().skip(1) {
                let expr_value = expr.generate_code2(&mut code_data);
                if expr_value == "c_0" {
                    compressed_table_coset = code_data.reuse_code(format!("({}*theta)", compressed_table_coset));
                } else {
                    compressed_table_coset = code_data.reuse_code(format!("({}*theta+{})", compressed_table_coset, expr_value));
                }
            }*/

            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            let right_gamma = code_data.reuse_code(format!("({} + gamma)", compressed_table_coset));

            if single_pass {
                post_code += &format!("t[{}] = ({} + beta) * {};\n", n, compressed_input_coset, right_gamma);
            } else {
                post_code += &format!("t_{}[i] = ({} + beta) * {};\n", n, compressed_input_coset, right_gamma);
            }
        }

        let mut code = "\n".to_string();
        if !single_pass {
            code += "let start = start_measure(format!(\"Allocs\"), true);\n";
            for idx in 0..pk.vk.cs.lookups.len() {
                code += &format!("let mut table_values_{} = vec![C::Scalar::zero(); size];\n", idx);
            }
            code += "stop_measure(start);\n\n";
        }

        code += "let start = start_measure(format!(\"Core evaluation\"), true);\n";

        for (idx, c) in code_data.constants.iter().enumerate() {
            code += &format!("let c_{} = {};\n", idx, scalar_to_string::<C::Scalar>(*c));
        }
        code += "\n";

        code += "let n = size;\n";
        code += "let num_threads = multicore::current_num_threads();\n";
        code += "let mut chunk = (n as usize) / num_threads;\n";
        code += "if chunk < num_threads {\n";
        code += "   chunk = n as usize;\n";
        code += "}\n";
        code += "\n";

        let mut ts = "v".to_string();
        let mut ps = "v".to_string();
        code += "multicore::scope(|scope| {\n";
        code += &format!("let v = values.chunks_mut(chunk);\n");
        if !single_pass {
            for idx in 0..pk.vk.cs.lookups.len() {
                code += &format!("let p_{} = table_values_{}.chunks_mut(chunk);\n", idx, idx);
                ts += &format!(", t_{}", idx);
                ps += &format!(", p_{}", idx);
            }
            code += "\n";
        }

        code += &format!("for (j, ({})) in izip!({}).enumerate() {{\n", ts, ps);
        code += "scope.spawn(move |_| {\n";
        code += "let start = j * chunk;\n";

        if single_pass {
            code += &format!("let mut t = vec![zero; {}];\n", pk.vk.cs.lookups.len());
        }

        code += "for i in 0..v.len() {\n";
        code += "let idx = i + start;\n\n";

        for (idx, c) in code_data.rotations.iter().enumerate() {
            code += &format!("let r_{} = (((idx as i32) + ({} * rot_scale)).rem_euclid(isize)) as usize;\n", idx, c);
        }

        let write_code = |code: &String| {
            let mut out = "".to_string();
            for c in code.chars() {
                if c == '<' {
                    out += &"i_";
                } else if c == '>' {
                    // don't do anything
                } else {
                    out += &c.to_string();
                }
            }
            out
        };

        for (idx, c) in code_data.results.iter().enumerate() {
            let mut part = write_code(&c.code);
            if part.starts_with("(") && part.ends_with(")") {
                part = part[1..part.len()-1].to_string();
            }
            code += &format!("let i_{} = {};  // {}\n", idx, part, c.counter);
        }
        code += "\n\n";

        code += &write_code(&post_code);

        if single_pass {
            code += "for n in 0..num_lookups {\n";
            code += "let product_coset = &product_cosets[n];\n";
            code += "let permuted_input_coset = &permuted_input_cosets[n];\n";
            code += "let permuted_table_coset = &permuted_table_cosets[n];\n";

            code += "let a_minus_s = permuted_input_coset[idx] - permuted_table_coset[idx];\n";
            code += "value = value * y + ((one - product_coset[idx]) * l0[idx]);\n";
            code += "value = value * y + ((product_coset[idx] * product_coset[idx] - product_coset[idx]) * l_last[idx]);\n";
            code += &format!("value = value * y + ((product_coset[{}] * (permuted_input_coset[idx] + beta) * (permuted_table_coset[idx] + gamma) - product_coset[idx] * t[n]) * l_active_row[idx]);\n", rot_next);
            code += "value = value * y + (a_minus_s * l0[idx]);\n";
            code += &format!("value = value * y + (a_minus_s * (permuted_input_coset[idx] - permuted_input_coset[{}]) * l_active_row[idx]);\n", rot_prev);
            code += "}\n";
        }

        code += "v[i] = value;\n";

        code += "}\n";
        code += "});\n";
        code += "}\n";
        code += "});\n";

        code += "stop_measure(start);\n\n";

        if !single_pass {
            let mut table_values_vec = "let table_values = vec![".to_string();
            for idx in 0..pk.vk.cs.lookups.len() {
                table_values_vec += &format!("table_values_{}, ", idx);
            }
            table_values_vec += "];\n";
            code += &table_values_vec;
        }

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
                        verify,
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
                .map(|lookup| lookup.commit_product(pk, params, beta, gamma, transcript, verify))
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
            &pk,
            &lookups,
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

    if verify {
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
                println!("*Incorrect Value [{}]: {:?} , {:?}", idx, h_poly.values[idx], h_poly_b.values[idx]);
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

    #[allow(unsafe_code)]
    unsafe {
        println!("·FFT: {}s", (FFT_TOTAL_TIME as f32)/1000000.0);
        println!("·MultiExps: {}s", (MULTIEXP_TOTAL_TIME as f32)/1000000.0);
        println!("·Evaluate: {}s", (EVALUATE_TOTAL_TIME as f32)/1000000.0);
    }

    proof
}