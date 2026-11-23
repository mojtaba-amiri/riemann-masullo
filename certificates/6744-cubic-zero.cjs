#!/usr/bin/env node
"use strict";

/*
 * A four-prime witness for mccorvie/riemann-masullo#6744.
 * Run with Node.js. All enclosure endpoints and quadrature weights use BigInt.
 *
 * For K = Q(cuberoot(2)), put A = sqrt(108)/(2*pi^(3/2)) and
 * xi(w) = 2*w*(w-1)*A^w*Gamma(w/2)*Gamma(w)*zeta_K(w).
 * Set s = 1/2+i*t. Functional equation and conjugation symmetry give
 * xi(s) = (1/pi) Re int_R xi(6+i*u)*exp((6+i*u-s)^2/128)/(6+i*u-s) du.
 * This adapts mlyle's Gaussian contour argument with the right line at 6
 * and a wider Gaussian. The ordinary Dedekind
 * functional equation and order-one growth suffice for the contour shift.
 * Original certificate: https://github.com/mccorvie/riemann-masullo/issues/6402#issuecomment-7101990468
 * Complex Stirling remainder: https://dlmf.nist.gov/5.11.ii
 *
 * For 2 and 3 the Euler denominators are 1-q (total ramification).
 * At 5 the polynomial X^3-2 has type (1,2); at 7 it is irreducible.
 * All other primes enter only in a degree-three absolute error estimate.
 * This script checks the arithmetic; it does not implement a Lean theorem.
 */

const UNIT = 1n << 96n;
const absInt = x => x < 0n ? -x : x;
const minInt = values => values.reduce((x, y) => x < y ? x : y);
const maxInt = values => values.reduce((x, y) => x > y ? x : y);

function floorDiv(a, b) {
  if (b === 0n) throw Error("division by zero");
  if (b < 0n) return floorDiv(-a, -b);
  return a / b - (a % b < 0n ? 1n : 0n);
}
const ceilDiv = (a, b) => -floorDiv(-a, b);
const point = value => [value, value];
const integer = n => point(BigInt(n) * UNIT);
function rational(n, d) {
  const numerator = BigInt(n) * UNIT;
  return [floorDiv(numerator, BigInt(d)), ceilDiv(numerator, BigInt(d))];
}

const add = (x, y) => [x[0] + y[0], x[1] + y[1]];
const neg = x => [-x[1], -x[0]];
const sub = (x, y) => add(x, neg(y));
const widen = (x, radius) => [x[0] - radius, x[1] + radius];
const magnitude = x => maxInt([absInt(x[0]), absInt(x[1])]);

function mul(x, y) {
  const values = x.flatMap(a => y.map(b => a * b));
  return [floorDiv(minInt(values), UNIT), ceilDiv(maxInt(values), UNIT)];
}
function div(x, y) {
  if (y[0] <= 0n && y[1] >= 0n) throw Error("divisor contains zero");
  const lo = x.flatMap(a => y.map(b => floorDiv(a * UNIT, b)));
  const hi = x.flatMap(a => y.map(b => ceilDiv(a * UNIT, b)));
  return [minInt(lo), maxInt(hi)];
}
function scaleInt(x, n) {
  n = BigInt(n);
  return n >= 0n ? [x[0] * n, x[1] * n] : [x[1] * n, x[0] * n];
}
function divInt(x, n) {
  n = BigInt(n);
  if (n === 0n) throw Error("division by zero");
  return n > 0n ? [floorDiv(x[0], n), ceilDiv(x[1], n)] : neg(divInt(x, -n));
}
function square(x) {
  const a = x[0] * x[0], b = x[1] * x[1];
  const lo = x[0] <= 0n && x[1] >= 0n ? 0n : minInt([a, b]);
  return [floorDiv(lo, UNIT), ceilDiv(maxInt([a, b]), UNIT)];
}
function cube(x) { return mul(mul(x, x), x); }

function integerSqrt(n) {
  if (n < 0n) throw Error("negative square root");
  if (n < 2n) return n;
  let x = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
  for (;;) {
    const next = (x + n / x) / 2n;
    if (next >= x) return x;
    x = next;
  }
}
function sqrt(x) {
  const lo = integerSqrt(x[0] * UNIT), hi = integerSqrt(x[1] * UNIT);
  return [lo, hi * hi === x[1] * UNIT ? hi : hi + 1n];
}

// The series guards below make each discarded tail smaller than one endpoint unit.
function atanSeries(x) {
  if (magnitude(x) > UNIT / 2n) throw Error("atan series outside its bound");
  const step = neg(mul(x, x));
  let term = x, sum = x;
  for (let k = 1; k < 56; k++) {
    term = mul(term, step);
    sum = add(sum, divInt(term, 2 * k + 1));
  }
  return widen(sum, 1n);
}
const pi = sub(scaleInt(atanSeries(rational(1, 5)), 16),
               scaleInt(atanSeries(rational(1, 239)), 4)); // Machin's identity
function atanPoint(v) {
  if (v < 0n) return neg(atanPoint(-v));
  const x = point(v);
  if (v <= UNIT / 2n) return atanSeries(x);
  return add(divInt(pi, 4), atanSeries(div(sub(x, integer(1)), add(x, integer(1)))));
}
const atan = x => [atanPoint(x[0])[0], atanPoint(x[1])[1]];

function logSeries(x) {
  const r = div(sub(x, integer(1)), add(x, integer(1)));
  if (magnitude(r) > UNIT / 2n) throw Error("log series outside its bound");
  const r2 = mul(r, r);
  let term = r, sum = r;
  for (let k = 1; k < 48; k++) {
    term = mul(term, r2);
    sum = add(sum, divInt(term, 2 * k + 1));
  }
  return widen(scaleInt(sum, 2), 1n);
}
const log2 = logSeries(integer(2));
function logPoint(v) {
  if (v <= 0n) throw Error("nonpositive logarithm");
  let x = point(v), k = 0;
  while (x[0] >= 2n * UNIT) { x = divInt(x, 2); k++; }
  while (x[1] < UNIT) { x = scaleInt(x, 2); k--; }
  return add(logSeries(x), scaleInt(log2, k));
}
const log = x => [logPoint(x[0])[0], logPoint(x[1])[1]];

function expPoint(v) {
  let x = point(v), k = 0;
  while (magnitude(x) > UNIT / 8n) { x = divInt(x, 2); k++; }
  let term = integer(1), sum = term;
  for (let j = 1; j <= 24; j++) {
    term = divInt(mul(term, x), j);
    sum = add(sum, term);
  }
  sum = widen(sum, 1n);
  while (k-- > 0) sum = mul(sum, sum);
  return sum;
}
const exp = x => [expPoint(x[0])[0], expPoint(x[1])[1]];

function cosSin(x) {
  const halfPi = divInt(pi, 2);
  const k = floorDiv((x[0] + x[1]) / 2n + halfPi[0] / 2n, halfPi[0]);
  const y = sub(x, scaleInt(halfPi, k));
  if (magnitude(y) > UNIT) throw Error("trigonometric reduction failed");
  const step = neg(mul(y, y));
  let cosTerm = integer(1), sinTerm = y, c = cosTerm, s = sinTerm;
  for (let j = 1; j <= 18; j++) {
    cosTerm = divInt(mul(cosTerm, step), 2 * j * (2 * j - 1));
    sinTerm = divInt(mul(sinTerm, step), 2 * j * (2 * j + 1));
    c = add(c, cosTerm);
    s = add(s, sinTerm);
  }
  c = widen(c, 1n);
  s = widen(s, 1n);
  switch (Number((k % 4n + 4n) % 4n)) {
    case 0: return [c, s];
    case 1: return [neg(s), c];
    case 2: return [neg(c), neg(s)];
    default: return [s, neg(c)];
  }
}

const real = x => [x, integer(0)];
const cadd = (z, w) => [add(z[0], w[0]), add(z[1], w[1])];
const csub = (z, w) => [sub(z[0], w[0]), sub(z[1], w[1])];
const cscale = (z, r) => [mul(z[0], r), mul(z[1], r)];
function cmul(z, w) {
  return [sub(mul(z[0], w[0]), mul(z[1], w[1])),
          add(mul(z[0], w[1]), mul(z[1], w[0]))];
}
function cinv(z) {
  const norm2 = add(square(z[0]), square(z[1]));
  return [div(z[0], norm2), div(neg(z[1]), norm2)];
}
const cdiv = (z, w) => cmul(z, cinv(w));
const cexp = z => cscale(cosSin(z[1]), exp(z[0]));
function rightHalfPlaneLog(z) {
  if (z[0][0] <= 0n) throw Error("complex logarithm outside the right half-plane");
  return [divInt(log(add(square(z[0]), square(z[1]))), 2), atan(div(z[1], z[0]))];
}

const halfLog2Pi = divInt(log(scaleInt(pi, 2)), 2);
function gamma(z) {
  // DLMF 5.11(i),(ii): after four correction terms the error at w=z+12
  // has modulus <= sec(arg(w)/2)^10 / (1188*|w|^9) <= 32/(1188*14^9).
  const w = cadd(z, real(integer(12)));
  if (w[0][0] < 14n * UNIT) throw Error("Stirling bound outside its domain");
  const inverse = cinv(w), inverse2 = cmul(inverse, inverse);
  let power = inverse;
  let value = cadd(csub(cmul(csub(w, real(rational(1, 2))), rightHalfPlaneLog(w)), w),
                   real(halfLog2Pi));
  for (const denominator of [12, -360, 1260, -1680]) {
    value = cadd(value, cscale(power, rational(1, denominator)));
    power = cmul(power, inverse2);
  }
  const error = rational(32n, 1188n * 14n ** 9n)[1];
  value = [widen(value[0], error), widen(value[1], error)];
  let recurrence = real(integer(1));
  for (let j = 0; j < 12; j++) recurrence = cmul(recurrence, cadd(z, real(integer(j))));
  return cdiv(cexp(value), recurrence);
}

function decimalBounds(x, digits = 9) {
  const decimal = 10n ** BigInt(digits);
  function format(value) {
    const prefix = value < 0n ? "-" : "";
    value = absInt(value);
    return prefix + (value / decimal) + "." + (value % decimal).toString().padStart(digits, "0");
  }
  return [format(floorDiv(x[0] * decimal, UNIT)), format(ceilDiv(x[1] * decimal, UNIT))];
}

const cut = 32, degree = 18, gridScale = 2 * degree;
const leftDistance = rational(11, 2); // 6 - 1/2
const logA = sub(sub(divInt(log(integer(108)), 2), log2), divInt(scaleInt(log(pi), 3), 2));
const eulerPrimes = [2, 3, 5, 7].map(p => ({
  p, logP: log(integer(p)), amplitude: rational(1n, BigInt(p) ** 6n)
}));
const one = real(integer(1));
const baseValues = new Map();

function baseIntegrand(index) {
  if (baseValues.has(index)) return baseValues.get(index);
  const u = rational(index, gridScale), w = [integer(6), u];
  let denominator = one;
  for (const {p, logP, amplitude} of eulerPrimes) {
    const q = cscale(cosSin(neg(mul(u, logP))), amplitude);
    let factor = csub(one, q);
    if (p === 5) factor = cmul(factor, csub(one, cmul(q, q)));
    if (p === 7) factor = csub(one, cmul(cmul(q, q), q));
    denominator = cmul(denominator, factor);
  }
  const arch = cmul(cmul(cexp(cscale(w, logA)), gamma(cscale(w, rational(1, 2)))), gamma(w));
  const poly = cmul(w, csub(w, one));
  const result = cdiv(cscale(cmul(arch, poly), integer(2)), denominator);
  baseValues.set(index, result);
  return result;
}
function integrand(index, t) {
  const displacement = [leftDistance, sub(rational(index, gridScale), integer(t))];
  const gaussian = cexp(cscale(cmul(displacement, displacement), rational(1, 128)));
  return cdiv(cmul(baseIntegrand(index), gaussian), displacement)[0];
}

function factorial(n) {
  let value = 1n;
  for (let k = 2; k <= n; k++) value *= BigInt(k);
  return value;
}
function gcd(a, b) { return b === 0n ? a : gcd(b, a % b); }

// Exact Newton-Cotes weights for one panel of length 1/2. Integrate each
// Lagrange polynomial on [0,1], then multiply by the panel length.
function panelWeights(n) {
  let lcm = 1n;
  for (let k = 1n; k <= BigInt(n + 1); k++) lcm = lcm / gcd(lcm, k) * k;
  return Array.from({length: n + 1}, (_, k) => {
    let coeff = [1n], denominator = 1n;
    for (let j = 0; j <= n; j++) {
      if (j === k) continue;
      const next = Array(coeff.length + 1).fill(0n);
      for (let i = 0; i < coeff.length; i++) {
        next[i] -= BigInt(j) * coeff[i];
        next[i + 1] += BigInt(n) * coeff[i];
      }
      coeff = next;
      denominator *= BigInt(k - j);
    }
    const numerator = coeff.reduce((sum, v, i) => sum + v * (lcm / BigInt(i + 1)), 0n);
    return rational(numerator, 2n * lcm * denominator);
  });
}
const weights = panelWeights(degree);
const weightSum = weights.reduce(add, integer(0));
if (weightSum[0] > UNIT / 2n || weightSum[1] < UNIT / 2n) throw Error("invalid weights");

function quadrature(t) {
  const samples = new Map();
  let total = integer(0);
  for (let panel = 0; panel < 4 * cut; panel++) {
    for (let j = 0; j <= degree; j++) {
      const index = (t - cut) * gridScale + panel * degree + j;
      if (!samples.has(index)) samples.set(index, integrand(index, t));
      total = add(total, mul(weights[j], samples.get(index)));
    }
  }
  return div(total, pi);
}

// On every unit disc around a node of the integration interval, Re(w) is in
// [5,7], |w| and |w-1| are <=43, |w-s|>=9/2, A^Re(w)<=1 and the Gaussian
// has norm <2. Splitting Euler's gamma integral at 1 bounds the two gammas
// by 7 and 721. The finite Euler product is at most zeta(5)^3<2.
// Thus 20,000,000 bounds the unnormalised integrand on each disc around
// every point of the interval. Cauchy's bound controls derivative n+1.
// On a unit panel, the product of distances to the n+1 equidistant nodes
// is <= n!/n^(n+1): between nodes j,j+1 use (j+1)!*(n-j)! <= n!.
// Rescale to length 1/2, integrate across 2*cut, then divide by pi.
const quadratureError = div(
  rational(BigInt(2 * cut) * 20000000n * factorial(degree), BigInt(2 * degree) ** BigInt(degree + 1)),
  pi
);

function isPrime(n) {
  for (let j = 2; j * j <= n; j++) if (n % j === 0) return false;
  return n >= 2;
}
function omittedRelativeError() {
  // The sum of residue degrees over p is at most 3. Sum p^-6 for
  // 7<p<=100 irrespective of splitting, then bound the rest by int_100^inf x^-6 dx.
  let sum = rational(1n, 5n * 100n ** 5n);
  for (let p = 8; p <= 100; p++) if (isPrime(p)) sum = add(sum, rational(1n, BigInt(p) ** 6n));
  const logTail = div(scaleInt(sum, 3), sub(integer(1), rational(1n, 8n ** 6n)));
  return sub(exp(logTail), integer(1));
}
const omitted = omittedRelativeError();
const zetaBound = cube(add(add(integer(1), rational(1, 64)), rational(1, 160)));
// zeta(6) <= 1 + 2^-6 + int_2^inf x^-6 dx.
const gammaBoundCache = new Map();
function gammaNormBound(a, numerator, denominator) {
  const key = [a, numerator, denominator].join("/");
  if (gammaBoundCache.has(key)) return gammaBoundCache.get(key);
  const y2 = square(rational(numerator, denominator));
  let product = integer(1);
  // |Gamma(a+i*y)| <= Gamma(a) / sqrt(prod_j(1+y^2/(a+j)^2)),
  // by recurrence and |Gamma(a+20+i*y)|<=Gamma(a+20).
  for (let j = 0; j < 20; j++) {
    product = mul(product, add(integer(1), div(y2, integer((a + j) ** 2))));
  }
  const bound = div(integer(factorial(a - 1)), sqrt(product));
  gammaBoundCache.set(key, bound);
  return bound;
}

function eulerError(t) {
  const grid = 8;
  const constant = div(scaleInt(mul(mul(exp(scaleInt(logA, 6)), exp(divInt(square(leftDistance), 128))), zetaBound), 2), pi);
  let total = integer(0);
  // Each length-1/8 cell supplies a rigorous elementary majorant for the modulus.
  for (let j = -cut * grid; j < cut * grid; j++) {
    const lo = j + t * grid, hi = lo + 1;
    const uMin = Math.max(0, lo, -hi), uMax = rational(Math.max(Math.abs(lo), Math.abs(hi)), grid);
    const vMin = rational(Math.max(0, j, -(j + 1)), grid);
    const poly = mul(sqrt(add(integer(36), square(uMax))), sqrt(add(integer(25), square(uMax))));
    const gammas = mul(gammaNormBound(3, uMin, 2 * grid), gammaNormBound(6, uMin, grid));
    const gaussian = exp(neg(divInt(square(vMin), 128)));
    const kernel = div(gaussian, sqrt(add(square(leftDistance), square(vMin))));
    total = add(total, divInt(mul(mul(poly, gammas), kernel), grid));
  }
  return mul(mul(total, constant), omitted);
}

// Write r=|u-t|>=32. Then |u|>=(29/32)r and |w|*|w-1|/|w-s|
// <=(41*40/32^2)r. Gamma recurrence with 10 and 18 shifts bounds the
// gamma product by 12!*23!*2^10 / |u|^28. Use A<1, the Gaussian bound
// exp((11/2)^2/128)<2, zeta(6)^3<2, and integrate over both tails.
const tailError = rational(9n * factorial(12) * factorial(23) * 2n ** 10n * 32n ** 2n,
                           26n * 29n ** 28n);

function check(t, lower, upper) {
  const finite = quadrature(t), euler = eulerError(t);
  const error = add(add(euler, quadratureError), tailError);
  const enclosure = widen(finite, error[1]);
  if (enclosure[0] <= lower[1] || enclosure[1] >= upper[0]) throw Error("endpoint sign certificate failed");
  return {
    t, finite: decimalBounds(finite), eulerErrorUpper: decimalBounds(euler)[1],
    quadratureErrorUpper: decimalBounds(quadratureError)[1], tailErrorUpper: decimalBounds(tailError)[1],
    enclosure: decimalBounds(enclosure)
  };
}
const results = [check(0, rational(2435, 1000), rational(2458, 1000)),
                 check(3, rational(-363, 10000), rational(-168, 10000))];
console.log(JSON.stringify(results, null, 2));
