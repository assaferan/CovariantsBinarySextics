/* Functions to be included in both hecke_matrix.c and hecke_eigenvalues.c */

#include <math.h>
#include <stdlib.h>
#include <string.h>
#include "ulong_extras.h"
#include "fmpz_vec.h"
#include "fmpz_mpoly.h"
#include "arb_mat.h"
#include "fmpz_mat.h"
#include "acb_poly.h"
#include "acb_mat.h"
#include "acb_theta.h"

/* Released FLINT (checked with 3.6) has no acb_theta_g2_covariants_lead and no ACB_THETA_G2_COV_NB;
   acb_theta_g2_covariants(..., lead = 1, ...) returns the leading coefficients as constant polynomials. */
#ifndef ACB_THETA_G2_COV_NB
#define ACB_THETA_G2_COV_NB 26
static void
acb_theta_g2_covariants_lead(acb_ptr res, const acb_poly_t f, slong prec)
{
    acb_poly_struct cov[ACB_THETA_G2_COV_NB];
    slong i;
    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
        acb_poly_init(cov + i);
    acb_theta_g2_covariants(cov, f, 1, prec);
    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
    {
        acb_poly_get_coeff_acb(res + i, cov + i, 0);
        acb_poly_clear(cov + i);
    }
}
#endif

/* ---------- Weights and cosets ---------- */

#define COV_K {1,2,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,7,7,8,9,10,10,12,15}
#define COV_J {6,0,4,8,2,6,8,12,0,4,6,10,2,4,8,0,6,6,2,4,2,4,0,2,2,0}

static void
get_p_from_q(slong* p, int* is_T1, slong q)
{
    if (n_is_prime(q))
    {
        *p = q;
        *is_T1 = 0;
    }
    else
    {
        if (!n_is_square(q))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q);
            flint_abort();
        }
        *p = n_sqrt(q);
        if (!n_is_prime(*p))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q);
            flint_abort();
        }
        *is_T1 = 1;
    }
}

static void
covariant_weight(slong* k, slong* j, const fmpz_mpoly_t pol, const fmpz_mpoly_ctx_t ctx)
{
    slong e[ACB_THETA_G2_COV_NB];
    slong klist[] = COV_K;
    slong jlist[] = COV_J;
    slong i;

    *k = 0;
    *j = 0;
    if (fmpz_mpoly_total_degree_si(pol, ctx) == 0)
    {
        return;
    }

    fmpz_mpoly_get_term_exp_si(e, pol, 0, ctx);
    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
    {
        *k += e[i] * klist[i];
        *j += e[i] * jlist[i];
    }
    *k -= (*j/2);
}

static void
hecke_rescale(acb_t f, slong k, slong j, slong p, int is_T1, slong prec)
{
    acb_set_si(f, p);
    if (is_T1)
    {
        acb_pow_si(f, f, 4 * k + 2 * j - 6, prec);
    }
    else
    {
        acb_pow_si(f, f, 2 * k + j - 3, prec);
    }
}

static slong
hecke_nb(slong p)
{
    return 1 + p + n_pow(p, 2) + n_pow(p, 3);
}

static slong hecke_nb_T1(slong p)
{
    return p + n_pow(p, 2) + n_pow(p, 3) + n_pow(p, 4);
}

/* Also return the sign in case of character as 0, 1 mod 2 */
static slong
hecke_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    fmpz_mat_zero(m);

    if (k < n_pow(p, 3))
    {
        /* Case 1 */
        a = k % p;
        b = (k / p) % p;
        c = (k / n_pow(p, 2)) % p;
        for (i = 0; i < 2; i++)
        {
            fmpz_one(fmpz_mat_entry(m, i, i));
        }
        for (i = 2; i < 4; i++)
        {
            fmpz_set_si(fmpz_mat_entry(m, i, i), p);
        }
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), c);
        return (a + b + c) % 2;
    }
    else if (k < 1 + n_pow(p, 3))
    {
        /* Case 2 */
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
        return 0;
    }
    else if (k < 1 + n_pow(p, 3) + p)
    {
        /* Case 3 */
        a = k - n_pow(p, 3) - 1;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), 1);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
        return (a) % 2;
    }
    else
    {
        /* Case 4 */
        a = (k - 1 - n_pow(p, 3) - p) % p;
        b = ((k - 1 - n_pow(p, 3) - p)/p) % p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), 1);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
        return (a + b) % 2;
    }
}

static slong
hecke_T1_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    fmpz_mat_zero(m);

    if (k == 0)
    {
        /* Case 1 */
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
        return 0;
    }
    else if (k < 1 + (n_pow(p, 2)-1) )
    {
        /* Case 2 */
        if (k < 1 + (p-1))
        {
            /* a is zero, b too, c is anything nonzero */
            a = 0;
            b = 0;
            c = k;
        }
        else
        {
            /* a is nonzero, b is anything, c is b^2/a */
            /* k-p is between 0 and p(p-1)-1 */
            a = (k-p) % (p-1);
            a += 1;
            b = (k-p) % p;
            c = (b*b) % p;
            c *= n_invmod(a, p);
            c = c % p;
        }
        for (i = 0; i < 4; i++) fmpz_set_si(fmpz_mat_entry(m, i, i), p);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), c);
        return (a + b + c) % 2;
    }
    else if (k < n_pow(p, 2) + p)
    {
        /* Case 3 */
        a = k - n_pow(p, 2);
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a*p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
        return a % 2;
    }
    else if (k < n_pow(p, 2) + p + n_pow(p, 3))
    {
        /* Case 4 */
        k = k - n_pow(p, 2) - p;
        b = k % p;
        a = k / p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), 1);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), -b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), -p*b);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
        return (a + b) % 2;
    }
    else
    {
        /* Case 5 */
        k = k - n_pow(p, 3) - n_pow(p, 2) - p;
        a = k%p;
        k = k/p;
        b = k%p;
        c = k/p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b*p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), 1);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), a*b+c);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a*p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), n_pow(p, 2));
        return (a + b + c) % 2;
    }
}

/* ---------- Context for multivariate polynomial evaluation ---------- */

static int
exp_le(const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (e1[k] > e2[k])
        {
            return 0;
        }
    }
    return 1;
}

static int
exp_lt_lex(const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (e1[k] > e2[k])
        {
            return 0;
        }
        if (e1[k] < e2[k])
        {
            return 1;
        }
    }
    return 0;
}

static void
exp_sub(slong* res, const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        res[k] = e1[k] - e2[k];
    }
}

static slong
exp_search(const slong* all_exps, slong bound, const slong* exp)
{
    slong low = 0;
    slong up = FLINT_MAX(0, bound - 1);
    slong mid;

    while (low < up)
    {
        mid = (up + low)/2;
        if (exp_lt_lex(all_exps + mid * ACB_THETA_G2_COV_NB, exp))
        {
            low = mid + 1;
        }
        else
        {
            up = mid;
        }
    }
    return low;
}

static int
exp_is_zero(const slong* exp)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (exp[k] != 0)
        {
            return 0;
        }
    }
    return 1;
}

struct hecke_mpoly_ctx_struct
{
    slong* all_exps;
    slong* add_chain;
    slong nb_exps;

    slong** indices;
    fmpz** coeffs;
    slong* nb_terms;
    slong* max_degrees;
    slong* ks;
    slong* js;
    slong lmax;
    slong nb_pols;
};

typedef struct hecke_mpoly_ctx_struct hecke_mpoly_ctx_t[1];

#define hecke_mpoly_ctx_exp(ctx, k) ((ctx)->all_exps + k * ACB_THETA_G2_COV_NB)

static void
hecke_mpoly_ctx_init(hecke_mpoly_ctx_t ctx, const fmpz_mpoly_vec_t pols,
    slong nb, const fmpz_mpoly_ctx_t mctx)
{
    fmpz_mpoly_t sum, m;
    fmpz_t c;
    slong* exp;
    slong k, j;
    int found;

    ctx->indices = flint_malloc(nb * sizeof(slong*));
    ctx->coeffs = flint_malloc(nb * sizeof(fmpz*));
    ctx->nb_terms = flint_malloc(nb * sizeof(slong));
    ctx->max_degrees = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));
    ctx->ks = flint_malloc(nb * sizeof(slong));
    ctx->js = flint_malloc(nb * sizeof(slong));
    ctx->nb_pols = nb;

    fmpz_mpoly_init(sum, mctx);
    fmpz_mpoly_init(m, mctx);
    fmpz_init(c);
    exp = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));

    /* Get nb_terms, lmax, max_degrees, weights */
    ctx->lmax = 0;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        ctx->max_degrees[k] = 0;
    }
    for (k = 0; k < nb; k++)
    {
        ctx->nb_terms[k] = fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, k), mctx);
        ctx->lmax = FLINT_MAX(ctx->lmax, ctx->nb_terms[k]);
        fmpz_mpoly_degrees_si(exp, fmpz_mpoly_vec_entry(pols, k), mctx);
        for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
        {
            ctx->max_degrees[j] = FLINT_MAX(ctx->max_degrees[j], exp[j]);
        }
        covariant_weight(&(ctx->ks[k]), &(ctx->js[k]), fmpz_mpoly_vec_entry(pols, k), mctx);
    }

    /* Make polynomial containing all monomials + powers of one variable */
    fmpz_one(c);
    for (k = 0; k < nb; k++)
    {
        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_monomial(m, fmpz_mpoly_vec_entry(pols, k), j, mctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, mctx);
        }
    }
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        for (j = 1; j <= ctx->max_degrees[k]; j++)
        {
            fmpz_mpoly_gen(m, k, mctx);
            fmpz_mpoly_pow_ui(m, m, j, mctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, mctx);
        }
    }

    /* Get all exponents */
    ctx->nb_exps = fmpz_mpoly_length(sum, mctx);
    ctx->all_exps = flint_malloc((ctx->nb_exps) * ACB_THETA_G2_COV_NB * sizeof(slong));
    ctx->add_chain = flint_malloc(2 * (ctx->nb_exps) * sizeof(slong));
    for (j = 0; j < ctx->nb_exps; j++)
    {
        fmpz_mpoly_get_term_exp_si(hecke_mpoly_ctx_exp(ctx, j), sum,
            ctx->nb_exps - 1 - j, mctx); /* terms are in revlex order. */
    }

    /* Make addition chain with the exponents we have */
    for (k = 0; k < ctx->nb_exps; k++)
    {
        found = 0;
        for (j = 0; (j < k) && !found; j++)
        {
            if (exp_is_zero(hecke_mpoly_ctx_exp(ctx, j)))
            {
                continue;
            }

            if (exp_le(hecke_mpoly_ctx_exp(ctx, j), hecke_mpoly_ctx_exp(ctx, k)))
            {
                exp_sub(exp, hecke_mpoly_ctx_exp(ctx, k), hecke_mpoly_ctx_exp(ctx, j));

                if (fmpz_mpoly_get_coeff_si_ui(sum, (ulong*) exp, mctx))
                {
                    found = 1;
                    ctx->add_chain[2 * k] = j;
                    ctx->add_chain[2 * k + 1] = exp_search(ctx->all_exps, k, exp);
                }
            }
        }

        if (!found)
        {
            ctx->add_chain[2 * k] = -1;
            ctx->add_chain[2 * k + 1] = -1;
        }
    }

    /* Get indices and coefficients */
    for (k = 0; k < nb; k++)
    {
        ctx->coeffs[k] = _fmpz_vec_init(ctx->nb_terms[k]);
        ctx->indices[k] = flint_malloc(2 * ctx->nb_terms[k] * sizeof(slong));

        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_coeff_fmpz(&ctx->coeffs[k][j],
                fmpz_mpoly_vec_entry(pols, k), j, mctx);
            fmpz_mpoly_get_term_exp_si(exp, fmpz_mpoly_vec_entry(pols, k), j, mctx);
            ctx->indices[k][j] = exp_search(ctx->all_exps, ctx->nb_exps, exp);
        }
    }

    fmpz_mpoly_clear(sum, mctx);
    fmpz_mpoly_clear(m, mctx);
    fmpz_clear(c);
    flint_free(exp);
}

static void
hecke_mpoly_ctx_clear(hecke_mpoly_ctx_t ctx)
{
    slong k;

    flint_free(ctx->add_chain);
    flint_free(ctx->all_exps);
    for (k = 0; k < ctx->nb_pols; k++)
    {
        _fmpz_vec_clear(ctx->coeffs[k], ctx->nb_terms[k]);
        flint_free(ctx->indices[k]);
    }
    flint_free(ctx->coeffs);
    flint_free(ctx->indices);
    flint_free(ctx->nb_terms);
    flint_free(ctx->max_degrees);
    flint_free(ctx->ks);
    flint_free(ctx->js);
}

static void
hecke_mpoly_eval(acb_ptr res, acb_srcptr val, const hecke_mpoly_ctx_t ctx, slong prec)
{
    acb_ptr* powers = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(acb_ptr));
    acb_ptr terms, temp;
    slong k, j;

    /* Get powers */
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        powers[k] = _acb_vec_init(ctx->max_degrees[k] + 1);
        _acb_vec_set_powers(powers[k], &val[k], ctx->max_degrees[k] + 1, prec);
    }
    terms = _acb_vec_init(ctx->nb_exps);
    temp = _acb_vec_init(ctx->lmax);

    /* Get all terms */
    for (k = 0; k < ctx->nb_exps; k++)
    {
        if (ctx->add_chain[2 * k] == -1)
        {
            acb_one(&terms[k]);
            for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
            {
                acb_mul(&terms[k], &terms[k],
                    &powers[j][ctx->all_exps[k * ACB_THETA_G2_COV_NB + j]], prec);
            }
        }
        else
        {
            acb_mul(&terms[k], &terms[ctx->add_chain[2 * k]],
                &terms[ctx->add_chain[2 * k + 1]], prec);
        }
    }

    /* Get dots */
    for (k = 0; k < ctx->nb_pols; k++)
    {
        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            acb_set(&temp[j], &terms[ctx->indices[k][j]]);
        }
        acb_dot_fmpz(&res[k], NULL, 0, temp, 1, ctx->coeffs[k], 1, ctx->nb_terms[k], prec);
    }

    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        _acb_vec_clear(powers[k], ctx->max_degrees[k] + 1);
    }
    flint_free(powers);
    _acb_vec_clear(terms, ctx->nb_exps);
    _acb_vec_clear(temp, ctx->lmax);
}

/* ---------- Base points ---------- */

static void
hecke_generate_base_points(acb_mat_struct* tau, slong max_dim, slong prec)
{
    flint_rand_t state;
    arb_mat_t x, y;
    arf_t t;
    slong k;

    flint_randinit(state);
    arf_init(t);
    arb_mat_init(x, 2, 2);
    arb_mat_init(y, 2, 2);

    for (k = 0; k < max_dim; k++)
    {
        /* Imaginary part is [1 + t, 1/4; 1/4, 1 + t] with 0<=t<=1 */
        arf_one(t);
        arf_mul_2exp_si(t, t, -2);
        arb_set_arf(arb_mat_entry(y, 0, 1), t);
        arb_set_arf(arb_mat_entry(y, 1, 0), t);
        arf_one(t);
        arf_mul_2exp_si(t, t, -n_clog(max_dim, 2));
        arf_mul_si(t, t, k, ARF_RND_NEAR, prec);
        arf_add_si(t, t, 1, prec, ARF_RND_NEAR);
        arb_set_arf(arb_mat_entry(y, 0, 0), t);
        arb_set_arf(arb_mat_entry(y, 1, 1), t);
        /* Real part is uniformly random in [0,1] */
        arf_urandom(arb_midref(arb_mat_entry(x, 0, 0)), state, prec, ARF_RND_NEAR);
        arf_urandom(arb_midref(arb_mat_entry(x, 0, 1)), state, prec, ARF_RND_NEAR);
        arb_set(arb_mat_entry(x, 1, 0), arb_mat_entry(x, 0, 1));
        arf_urandom(arb_midref(arb_mat_entry(x, 1, 1)), state, prec, ARF_RND_NEAR);
        acb_mat_set_real_imag(&tau[k], x, y);
        /* acb_mat_printd(&tau[k], 5); */
    }

    flint_randclear(state);
    arf_clear(t);
    arb_mat_clear(x);
    arb_mat_clear(y);
}

/* ---------- Read input ---------- */

static void
parse_integers(slong* nb_spaces, slong** dims, int** characters, const char* filename_in)
{
    FILE* file_in;
    char* str;
    size_t nb, nb_prev;
    slong dim;

    file_in = fopen(filename_in, "r");
    if (file_in == NULL)
    {
        flint_printf("Error: could not read file %s\n", filename_in);
        flint_abort();
    }

    *nb_spaces = 0;
    dim = 0;
    nb_prev = 0;

    while (!feof(file_in))
    {
        str = NULL;
        nb = 0;
        getline(&str, &nb, file_in);
        str[strcspn(str, "\n")] = 0; /* remove final newline */
        nb = strcspn(str, "");
        flint_free(str);

        if (nb > 0 && nb_prev == 0)
        {
            /* start new space */
            (*nb_spaces)++;
            *dims = flint_realloc(*dims, (*nb_spaces + 1) * sizeof(slong));
            *characters = flint_realloc(*characters, (*nb_spaces + 1) * sizeof(int));
            dim = 0;

            /* get character */
            str = NULL;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            nb = strcspn(str, "");
            (*characters)[*nb_spaces - 1] = (int) strtol(str, NULL, 10);
            flint_free(str);
        }
        else if (nb > 0)
        {
            dim++;
        }
        else if (nb == 0 && nb_prev > 0)
        {
            (*dims)[*nb_spaces - 1] = dim;
            dim = 0;
        }
        nb_prev = nb;
    }

    if (nb_prev > 0)
    {
        (*dims)[*nb_spaces - 1] = dim;
        dim = 0;
    }
    fclose(file_in);
}
