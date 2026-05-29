//
// Discrete Logarithm Problem in Z*p:
//     y = g^x (mod p)
//
// In Z*p, x is usually in set of [2, p-2]

use std::collections::HashMap;

use rug::Integer;
// use rug::ops::Pow;

fn main() {
    // let y = Integer::from(11);
    // let g = Integer::from(5);
    // let p = Integer::from(23);

    // let g = Integer::from(17);
    // let y = Integer::from(2);
    // let p: Integer = Integer::from(158) * (Integer::from(2).pow(800u32) + 25) + 1;

    let g = Integer::from(7u64);
    let p = Integer::from(1_073_741_827u64); // простое, ~2^30
    let x_real = Integer::from(987_654_321u64);
    let y = g.clone().pow_mod(&x_real, &p).unwrap();

    println!("Given {} = {}^x (mod {}):", y, g, p);

    println!("  [Index Calculus]");
    match index_calculus(&y, &g, &p) {
        Ok(x) => println!("    x = {}", x),
        Err(_) => println!("    x is not found"),
    }

    println!("  [Shanks BSGS]");
    match shanks(&y, &g, &p) {
        Ok(x) => println!("    x = {}", x),
        Err(_) => println!("    x is not found"),
    }

    println!("  [Pollard rho]");
    match pollard_rho(&y, &g, &p) {
        Ok(x) => println!("    x = {}", x),
        Err(_) => println!("    x is not found"),
    }
}

// Pollard rho for DLP, O(sqrt(p)) expected time, O(1) memory.
// Order of g is taken as n = p-1 (g must be a primitive root mod p).
#[allow(dead_code)]
fn pollard_rho(y: &Integer, g: &Integer, p: &Integer) -> Result<Integer, Integer> {
    let n = Integer::from(p - 1);

    let step = |x: &Integer, a: &Integer, b: &Integer| -> (Integer, Integer, Integer) {
        let bucket = Integer::from(x % 3).to_i32().unwrap_or(0);
        match bucket {
            0 => {
                // x' = y*x, a' = a, b' = b+1
                let nx = Integer::from(y * x).modulo(p);
                let nb = Integer::from(b + 1).modulo(&n);
                (nx, a.clone(), nb)
            }
            1 => {
                // x' = x^2, a' = 2a, b' = 2b
                let nx = x.clone().pow_mod(&Integer::from(2), p).unwrap();
                let na = Integer::from(a * 2).modulo(&n);
                let nb = Integer::from(b * 2).modulo(&n);
                (nx, na, nb)
            }
            _ => {
                // x' = g*x, a' = a+1, b' = b
                let nx = Integer::from(g * x).modulo(p);
                let na = Integer::from(a + 1).modulo(&n);
                (nx, na, b.clone())
            }
        }
    };

    let (mut x1, mut a1, mut b1) = (Integer::from(1), Integer::from(0), Integer::from(0));
    let (mut x2, mut a2, mut b2) = (x1.clone(), a1.clone(), b1.clone());

    let limit = Integer::from(p - 1);
    let mut iter = Integer::from(0);

    while iter < limit {
        let (nx1, na1, nb1) = step(&x1, &a1, &b1);
        x1 = nx1; a1 = na1; b1 = nb1;

        let (nx2, na2, nb2) = step(&x2, &a2, &b2);
        let (nx2, na2, nb2) = step(&nx2, &na2, &nb2);
        x2 = nx2; a2 = na2; b2 = nb2;

        if x1 == x2 {
            // y^(b1-b2) ≡ g^(a2-a1) (mod p), with y = g^x:
            // x*(b1-b2) ≡ (a2-a1) (mod n)
            let lhs = Integer::from(&a2 - &a1).modulo(&n);
            let rhs = Integer::from(&b1 - &b2).modulo(&n);

            let d: Integer = rhs.clone().gcd(&n);
            if d == 0 {
                return Err(y.clone());
            }
            if Integer::from(&lhs % &d) != 0 {
                return Err(y.clone());
            }
            let lhs_r = Integer::from(&lhs / &d);
            let rhs_r = Integer::from(&rhs / &d);
            let n_r = Integer::from(&n / &d);

            let inv = match rhs_r.invert(&n_r) {
                Ok(v) => v,
                Err(_) => return Err(y.clone()),
            };
            let x0 = Integer::from(&lhs_r * &inv).modulo(&n_r);

            // d candidates: x0 + k*n_r, verify g^x ≡ y.
            let mut k = Integer::from(0);
            while k < d {
                let cand = Integer::from(&x0 + Integer::from(&k * &n_r)).modulo(&n);
                let test = g.clone().pow_mod(&cand, p).unwrap();
                if &test == y {
                    return Ok(cand);
                }
                k += 1;
            }
            return Err(y.clone());
        }
        iter += 1;
    }

    Err(y.clone())
}

#[allow(dead_code)]
fn shanks(y: &Integer, g: &Integer, p: &Integer) -> Result<Integer, Integer> {
    let mut s = HashMap::<Integer, Integer>::new();
    let mut t = HashMap::<Integer, Integer>::new();

    let m: Integer = Integer::from(p - 1).sqrt() + 1;

    let mut i: Integer = Integer::from(0);
    while i <= m {
        let i_int = i.clone();
        let exp = Integer::from(&i_int * &m);
        let key_s = g.clone().pow_mod(&exp, p).unwrap();
        s.insert(key_s, i_int.clone());

        let gi = g.clone().pow_mod(&i_int, p).unwrap();
        let key_t = Integer::from(y * &gi).modulo(p);
        t.insert(key_t, i_int);

        i += 1;
    }

    for (k, vs) in &s {
        if let Some(vt) = t.get(k) {
            let x = Integer::from(vs * &m) - vt;
            return Ok(x.modulo(p));
        }
    }

    Err(y.clone())
}

#[allow(dead_code)]
fn exhaustive(y: &Integer, g: &Integer, p: &Integer) -> Result<Integer, Integer> {
    let mut x = Integer::from(2);
    let upper = Integer::from(p - 2);

    while x <= upper {
        let gx = g.clone().pow_mod(&x, p).unwrap();

        if &gx == y {
            return Ok(x);
        }

        x += 1;
    }

    Err(y.clone())
}

// ─── number theory helpers ────────────────────────────────────────────────────

/// Extended GCD: returns (g, x, y) with a*x + b*y = g.
fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x1, y1) = extended_gcd(b, a % b);
        (g, y1, x1 - (a / b) * y1)
    }
}

/// Modular inverse of a mod m (returns None if gcd != 1).
fn mod_inv(a: i64, m: i64) -> Option<i64> {
    let (g, x, _) = extended_gcd(a.rem_euclid(m), m);
    if g != 1 { None } else { Some(x.rem_euclid(m)) }
}

/// Factorise n into Vec<(prime, exponent)>.
fn factorize(mut n: i64) -> Vec<(i64, u32)> {
    let mut factors = Vec::new();
    let mut d = 2i64;
    while d * d <= n {
        if n % d == 0 {
            let mut e = 0u32;
            while n % d == 0 { n /= d; e += 1; }
            factors.push((d, e));
        }
        d += 1;
    }
    if n > 1 { factors.push((n, 1)); }
    factors
}

/// CRT: given remainders `rs` and moduli `ms` (pairwise coprime),
/// returns x with x ≡ rs[i] (mod ms[i]) and the combined modulus.
fn crt(rs: &[i64], ms: &[i64]) -> Option<(i64, i64)> {
    let mut r = rs[0].rem_euclid(ms[0]);
    let mut m = ms[0];
    for (&ri, &mi) in rs[1..].iter().zip(ms[1..].iter()) {
        let (g, p, _) = extended_gcd(m, mi);
        if (ri - r) % g != 0 { return None; }
        let lcm = m / g * mi;
        r = (r + m * (((ri - r) / g * p).rem_euclid(mi / g))).rem_euclid(lcm);
        m = lcm;
    }
    Some((r, m))
}

// ─── trial division ───────────────────────────────────────────────────────────

/// Returns Some(exponents) if val is B-smooth over `base`, else None.
fn try_factor(val: &Integer, base: &[u64]) -> Option<Vec<i64>> {
    let mut rem = val.clone();
    let mut exps = vec![0i64; base.len()];
    for (i, &pb) in base.iter().enumerate() {
        let prime = Integer::from(pb);
        while Integer::from(&rem % &prime) == 0 {
            rem /= &prime;
            exps[i] += 1;
        }
    }
    if rem == 1 { Some(exps) } else { None }
}

// ─── linear system solver over Z/nZ via CRT ──────────────────────────────────
//
// n = p-1 is typically composite.  We solve mod each prime-power factor of n
// using standard Gaussian elimination over Z/q^eZ (where q is prime, so the
// ring is "almost" a field), then combine with CRT.
//
// For each prime-power q^e dividing n:
//   • reduce all coefficients mod q^e
//   • do Gaussian elimination, treating non-invertible pivots carefully:
//     divide through by the common factor of q to lower the modulus
//   • record partial solutions
// Finally CRT-combine partial solutions for each unknown.

/// Solve Ax ≡ b (mod q^e) by Gaussian elimination.
/// A is rows×cols matrix, b is the RHS column.
/// Returns a vector of length `cols` with solutions (or 0 if undetermined).
fn solve_mod_prime_power(
    a: &[Vec<i64>],
    b: &[i64],
    cols: usize,
    q: i64,
    e: u32,
) -> (Vec<i64>, i64) {
    let modulus = q.pow(e);
    let rows = a.len();

    // Working matrix [A | b] with entries in Z/modulus
    let mut mat: Vec<Vec<i64>> = a
        .iter()
        .zip(b.iter())
        .map(|(row, &rhs)| {
            let mut r: Vec<i64> = row.iter().map(|&x| x.rem_euclid(modulus)).collect();
            r.push(rhs.rem_euclid(modulus));
            r
        })
        .collect();

    let mut pivot_col = vec![usize::MAX; cols]; // pivot_col[var] = row that solved it
    let mut pivot_row = 0usize;

    for col in 0..cols {
        if pivot_row >= rows { break; }

        // Find row where mat[r][col] is invertible mod modulus (gcd == 1)
        let inv_row = (pivot_row..rows).find(|&r| {
            let g = extended_gcd(mat[r][col].rem_euclid(modulus), modulus).0;
            g == 1
        });

        if let Some(r) = inv_row {
            mat.swap(pivot_row, r);
            let inv = mod_inv(mat[pivot_row][col], modulus).unwrap();
            // Normalise pivot row
            for c in 0..=cols {
                mat[pivot_row][c] = (mat[pivot_row][c] * inv).rem_euclid(modulus);
            }
            // Eliminate column in all other rows
            for row in 0..rows {
                if row == pivot_row || mat[row][col] == 0 { continue; }
                let factor = mat[row][col];
                for c in 0..=cols {
                    mat[row][c] = (mat[row][c] - factor * mat[pivot_row][c]).rem_euclid(modulus);
                }
            }
            pivot_col[col] = pivot_row;
            pivot_row += 1;
        }
        // If no invertible pivot: variable undetermined mod this prime-power → leave as 0
    }

    // Extract solution
    let mut sol = vec![0i64; cols];
    for (col, &pr) in pivot_col.iter().enumerate() {
        if pr != usize::MAX {
            sol[col] = mat[pr][cols].rem_euclid(modulus);
        }
    }
    (sol, modulus)
}

/// Solve the full system mod n = ∏ q_i^e_i via CRT.
/// Returns HashMap<variable_index → value mod n>.
fn solve_system(
    a: &[Vec<i64>],
    b: &[i64],
    cols: usize,
    n: i64,
) -> HashMap<usize, i64> {
    let factors = factorize(n);
    // For each variable, collect (residue, modulus) pairs from each prime-power
    let mut residues: Vec<Vec<(i64, i64)>> = vec![Vec::new(); cols];

    for (q, e) in &factors {
        let (sol, modulus) = solve_mod_prime_power(a, b, cols, *q, *e);
        for (var, &val) in sol.iter().enumerate() {
            residues[var].push((val, modulus));
        }
    }

    let mut result = HashMap::new();
    for (var, parts) in residues.iter().enumerate() {
        if parts.is_empty() { continue; }
        let rs: Vec<i64> = parts.iter().map(|&(r, _)| r).collect();
        let ms: Vec<i64> = parts.iter().map(|&(_, m)| m).collect();
        if let Some((val, _)) = crt(&rs, &ms) {
            result.insert(var, val.rem_euclid(n));
        }
    }
    result
}

// ─── Sieve of Eratosthenes ────────────────────────────────────────────────────

fn sieve_primes(bound: u64) -> Vec<u64> {
    if bound < 2 { return vec![]; }
    let n = bound as usize + 1;
    let mut is_prime = vec![true; n];
    is_prime[0] = false; is_prime[1] = false;
    let mut i = 2usize;
    while i * i < n {
        if is_prime[i] {
            let mut j = i * i;
            while j < n { is_prime[j] = false; j += i; }
        }
        i += 1;
    }
    (2..n).filter(|&i| is_prime[i]).map(|i| i as u64).collect()
}

// ─── Index Calculus ───────────────────────────────────────────────────────────

pub fn index_calculus(y: &Integer, g: &Integer, p: &Integer) -> Result<Integer, String> {
    let n_big = Integer::from(p - 1); // order of Z*p
    let n = n_big.to_i64().ok_or("p-1 exceeds i64")?;

    // Factor base: all primes up to B
    let ln_p = (p.to_f64()).ln();
    let b_bound = ((ln_p.sqrt() * ln_p.ln().sqrt()) as u64).max(23).min(300);
    let base = sieve_primes(b_bound);
    let base_len = base.len();

    // ── Phase 1: collect relations ──────────────────────────────────────────
    // g^k ≡ ∏ p_i^{e_i}  (mod p)
    // ⟹  k ≡ ∑ e_i · log_g(p_i)  (mod n)
    // We collect these as rows of the linear system A·x ≡ b (mod n),
    // where x[i] = log_g(base[i]).

    let relations_needed = base_len + 20;
    let mut a_rows: Vec<Vec<i64>> = Vec::new();
    let mut b_col: Vec<i64> = Vec::new();

    let mut k = 1i64;
    let mut attempts = 0usize;
    let max_attempts = relations_needed * 500;

    while a_rows.len() < relations_needed && attempts < max_attempts {
        k = (k + 1) % n;
        attempts += 1;

        let k_big = Integer::from(k);
        let gk = g.clone().pow_mod(&k_big, p).unwrap();

        if let Some(exps) = try_factor(&gk, &base) {
            let row: Vec<i64> = exps.iter().map(|&e| e.rem_euclid(n)).collect();
            a_rows.push(row);
            b_col.push(k.rem_euclid(n));
        }
    }

    if a_rows.len() < base_len {
        return Err(format!(
            "not enough relations ({} collected, need {})",
            a_rows.len(), base_len
        ));
    }

    // ── Solve system mod n via CRT over prime-power factors of n ───────────
    let logs_i64 = solve_system(&a_rows, &b_col, base_len, n);

    // Build prime → log_g(prime) map; verify each log
    let mut prime_logs: HashMap<u64, Integer> = HashMap::new();
    for (i, &pb) in base.iter().enumerate() {
        if let Some(&l) = logs_i64.get(&i) {
            let l_big = Integer::from(l);
            // Quick sanity check: g^l ≡ pb (mod p)?
            let check = g.clone().pow_mod(&l_big, p).unwrap();
            if check == Integer::from(pb) {
                prime_logs.insert(pb, l_big);
            }
        }
    }

    // ── Phase 2: individual log ─────────────────────────────────────────────
    // Find s so that y·g^s (mod p) factors over the base.
    // Then log_g(y) = ∑ e_i·log_g(p_i) − s  (mod n).
    let max_s = (relations_needed * 1000) as i64;
    for s in 0..max_s {
        let s_big = Integer::from(s);
        let gs = g.clone().pow_mod(&s_big, p).unwrap();
        let ygs = Integer::from(y * &gs).modulo(p);

        if let Some(exps) = try_factor(&ygs, &base) {
            let mut log_sum = Integer::from(0u32);
            let mut all_known = true;

            for (i, &e) in exps.iter().enumerate() {
                if e == 0 { continue; }
                match prime_logs.get(&base[i]) {
                    Some(l) => {
                        log_sum += Integer::from(e) * l;
                        log_sum = log_sum.modulo(&n_big);
                    }
                    None => { all_known = false; break; }
                }
            }
            if !all_known { continue; }

            let x = Integer::from(&log_sum - s).modulo(&n_big);

            // Verify
            let check = g.clone().pow_mod(&x, p).unwrap();
            if &check == y {
                return Ok(x);
            }
        }
    }

    Err("individual log phase failed".to_string())
}
