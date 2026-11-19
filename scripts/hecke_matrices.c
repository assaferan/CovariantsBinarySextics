/* Usage:
./hecke_matrices.exe q filename_in filename_out

Each block of lines in filename_in encodes a space of modular forms. Different
spaces should be separated by one newline. Each space consists of following
line: (1) Text description, (2) 1 or 0 depending on whether the space has
character or not, (3) one line per covariant as a multivariate polynomial in
Co16, etc. with integral coefficients.

A list of matrices is printed to filename_out. Each one encodes the Hecke
action (T(p) if q=p is prime, T_1(p^2) if q=p^2) on the input space as a matrix
with rational coefficients. If a given matrix is proved to be integral by other
means, then the result is integral and certified. */

#include <gmp.h>    /* before the flint headers, for their mpz functions */
#include "fmpq.h"
#include "fmpq_mat.h"
#include "hecke.c"

/* ---------- Read input ---------- */

static void
parse_covariants(fmpz_mpoly_vec_t pols, slong nb_spaces, const slong* dims,
    const slong* pols_indices, const char* filename_in, const fmpz_mpoly_ctx_t ctx)
{
    char** vars;
    char* str;
    size_t nb = 0;
    FILE* file_in;
    slong inds[ACB_THETA_G2_COV_NB] = {16, 20, 24, 28, 32, 36, 38, 312, 40, 44, 46, 410, 52, 54, 58, 60, 661, 662, 72, 74, 82, 94, 100, 102, 122, 150};
    slong k, j;

    vars = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(char*));
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        vars[k] = flint_malloc(6 * sizeof(char));
        flint_sprintf(vars[k], "Co%wd", inds[k]);
    }

    file_in = fopen(filename_in, "r");
    if (file_in == NULL)
    {
        flint_printf("Error: could not read file %s\n", filename_in);
        flint_abort();
    }

    for (k = 0; k < nb_spaces; k++)
    {
        str = NULL;
        getline(&str, &nb, file_in);
        flint_free(str); /* Text description */
        str = NULL;
        getline(&str, &nb, file_in);
        flint_free(str); /* Character */

        for (j = 0; j < dims[k]; j++)
        {
            str = NULL;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            fmpz_mpoly_set_str_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                str, (const char**) vars, ctx);
            flint_free(str);
            flint_printf("(parse_covariants) k = %wd, j = %wd, poly:\n", k, j);
            fmpz_mpoly_print_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                (const char**) vars, ctx);
            flint_printf("\n");
        }

        if (!feof(file_in))
        {
            str = NULL;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            nb = strcspn(str, "");
            if (nb != 0)
            {
                flint_printf("(parse_covariants) Error: no empty line after k = %wd, dim = %wd\n",
                    k, dims[k]);
            }
            flint_free(str);
        }
    }

    fclose(file_in);
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        flint_free(vars[k]);
    }
    flint_free(vars);
}

/* ---------- Recognize rational numbers ---------- */

static void
cont_frac_get_fmpq(fmpq_t c, fmpz* r_vec, slong nb_steps)
{
    slong k;
    fmpq_zero(c);
    fmpq_add_fmpz(c, c, &r_vec[nb_steps-1]);
    for (k = nb_steps-2; k >= 0; k--)
    {
        fmpq_inv(c, c);
        fmpq_add_fmpz(c, c, &r_vec[k]);
    }
}

static int
cont_frac_step(fmpz_t r, arf_t next, const arf_t current, slong prec, slong tol_exp)
{
    int res = 0;
    arf_get_fmpz(r, current, ARF_RND_FLOOR);
    arf_sub_fmpz(next, current, r, prec, ARF_RND_NEAR);
    if (arf_cmp_2exp_si(next, tol_exp) < 0)
    {
        res = 1;
    }
    else
    {
        arf_ui_div(next, 1, next, prec, ARF_RND_NEAR);
    }
    return res;
}

static int
arf_get_approx_fmpq(fmpq_t y, const arf_t x, slong prec)
{
    arf_t z;
    int res = 1;
    int stop = 0;
    slong max_steps = prec / 2;
    fmpz* r_vec;
    slong k;

    arf_init(z);
    r_vec = _fmpz_vec_init(max_steps);

    arf_set(z, x);
    k = 0;
    for (k = 0; (k < max_steps) && !stop; k++)
    {
        stop = cont_frac_step(&r_vec[k], z, z, prec, -prec / 8);
    }

    if (k == max_steps)
    {
        res = 0;
    }
    else
    {
        res = 1;
        cont_frac_get_fmpq(y, r_vec, k);
    }

    arf_clear(z);
    _fmpz_vec_clear(r_vec, max_steps);
    return res;
}

static int
arb_get_approx_fmpq(fmpq_t y, const arb_t x, slong prec)
{
    int res;
    mpz_t n, d;
    fmpz_t c;
    arb_t z;

    mpz_init(n);
    mpz_init(d);
    fmpz_init(c);
    arb_init(z);

    res = arf_get_approx_fmpq(y, arb_midref(x), prec);

    if (res)
    {
        fmpq_get_mpz_frac(n, d, y);
        fmpz_set_mpz(c, d);
        arb_mul_fmpz(z, x, c, prec);
        res = (mag_cmp_2exp_si(arb_radref(z), - prec/8) < 0);
    }

    mpz_clear(n);
    mpz_clear(d);
    fmpz_clear(c);
    arb_clear(z);
    return res;
}

static int
acb_get_approx_fmpq(fmpq_t y, const acb_t x, slong prec)
{
    int res = 0;
    mag_t im;

    mag_init(im);
    arb_get_mag(im, acb_imagref(x));

    if (mag_cmp_2exp_si(im, -prec / 8) < 0)
    {
        res = arb_get_approx_fmpq(y, acb_realref(x), prec);
    }

    mag_clear(im);
    return res;
}

/* ---------- Print output ---------- */

/* This is copied from flint/src/fmpz_mat/io.c */
#define xxx_putc(c)        \
do {                       \
    z = fputc((c), file);  \
    if (z <= 0)            \
        return z;          \
} while (0)

#define xxx_fmpq_print(f)        \
do {                             \
    z = fmpq_fprint(file, (f));  \
    if (z <= 0)                  \
        return z;                \
} while(0)

int fmpq_mat_fprint_pretty(FILE * file, const fmpq_mat_t mat)
{
    int z;
    slong i, j;
    slong r = mat->r;
    slong c = mat->c;

    xxx_putc('[');
    for (i = 0; i < r; i++)
    {
        xxx_putc('[');
        for (j = 0; j < c; j++)
        {
            xxx_fmpq_print(fmpq_mat_entry(mat, i, j));
            if (j != c - 1)
                xxx_putc(' ');
        }
        xxx_putc(']');
        xxx_putc('\n');
    }
    xxx_putc(']');

    return z;
}

#undef xxx_putc
#undef xxx_fmpq_print

/* ---------- Numerical Hecke action ---------- */

/* Add term corresponding to k^th coset to all matrices */
static void
hecke_add_term(acb_mat_struct* hecke, slong nb_spaces, const slong* dims,
    const int* characters, const slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, slong k, slong p,
    int is_T1, const hecke_mpoly_ctx_t ctx, slong prec)
{
    fmpz_mat_t mat;
    acb_mat_t w, c, cinv;
    acb_poly_t r;
    acb_ptr basic;
    acb_ptr res;
    slong nb = pols_indices[nb_spaces];
    acb_t chi5, det;
    slong i, j, l, s;

    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);
    acb_mat_init(c, 2, 2);
    acb_mat_init(cinv, 2, 2);
    acb_poly_init(r);
    acb_init(chi5);
    acb_init(det);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);
    res = _acb_vec_init(nb);

    if (is_T1)
    {
        s = hecke_T1_coset(mat, k, p);
    }
    else
    {
        s = hecke_coset(mat, k, p);
    }

    for (j = 0; j < max_dim; j++)
    {
        acb_siegel_transform_cocycle_inv(w, c, cinv, mat, &taus[j], prec);
        acb_theta_g2_sextic_chi5(r, chi5, w, prec);
        acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
        acb_mat_det(det, cinv, prec);
        acb_pow_ui(det, det, 5, prec);
        acb_mul(chi5, chi5, det, prec);
        acb_theta_g2_covariants_lead(basic, r, prec);
        hecke_mpoly_eval(res, basic, ctx, prec);

        flint_printf("k = %wd, got s = %wd, rescaled chi5: ", k, s);
        acb_printd(chi5, 5);
        flint_printf("\n");

        for (i = 0; i < nb_spaces; i++)
        {
            if (j >= dims[i])
            {
                continue;
            }
            if (characters[i])
            {
                if (p == 2 && k < 8)
                {
                    flint_printf("skipped\n");
                    continue;
                }
                if (s == 1)
                {
                    _acb_vec_neg(res + pols_indices[i], res + pols_indices[i], dims[i]);
                }
                _acb_vec_scalar_mul(res + pols_indices[i], res + pols_indices[i],
                    dims[i], chi5, prec);
            }
            for (l = 0; l < dims[i]; l++)
            {
                acb_add(acb_mat_entry(&hecke[i], l, j),
                    acb_mat_entry(&hecke[i], l, j), &res[pols_indices[i] + l], prec);
            }
        }
    }

    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    acb_mat_clear(c);
    acb_mat_clear(cinv);
    acb_poly_clear(r);
    acb_clear(chi5);
    acb_clear(det);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
    _acb_vec_clear(res, nb);
}

static void
hecke_source(acb_mat_struct* source, slong nb_spaces, const slong* dims,
    const int* characters, const slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, const hecke_mpoly_ctx_t ctx, slong prec)
{
    acb_poly_t r;
    acb_ptr basic;
    acb_ptr res;
    acb_t chi5;
    slong i, j, l;
    slong nb = pols_indices[nb_spaces];

    acb_poly_init(r);
    acb_init(chi5);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);
    res = _acb_vec_init(nb);

    for (j = 0; j < max_dim; j++)
    {
        acb_theta_g2_sextic_chi5(r, chi5, &taus[j], prec);
        acb_theta_g2_covariants_lead(basic, r, prec);
        hecke_mpoly_eval(res, basic, ctx, prec);

        for (i = 0; i < nb_spaces; i++)
        {
            if (j >= dims[i])
            {
                continue;
            }
            if (characters[i])
            {
                _acb_vec_scalar_mul(res + pols_indices[i], res + pols_indices[i],
                    dims[i], chi5, prec);
            }
            for (l = 0; l < dims[i]; l++)
            {
                acb_set(acb_mat_entry(&source[i], l, j), &res[pols_indices[i] + l]);
            }
        }
    }

    flint_printf("got source:\n");
    acb_mat_printd(source, 5);

    acb_poly_clear(r);
    acb_clear(chi5);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
    _acb_vec_clear(res, nb);
}


static int
hecke_attempt(fmpq_mat_struct* mats, slong nb_spaces, const slong* dims,
    const int* characters, const slong* pols_indices, slong max_dim, slong p, int is_T1,
    const hecke_mpoly_ctx_t ctx, slong prec)
{
    acb_mat_struct* tau;
    acb_mat_struct* hecke;
    acb_mat_struct* source;
    acb_t f;
    slong k, j, l;
    slong k0, j0;
    slong nb = (is_T1 ? hecke_nb_T1(p) : hecke_nb(p));
    int res = 1;

    /* Init */
    tau = flint_malloc(max_dim * sizeof(acb_mat_struct));
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_init(&tau[k], 2, 2);
    }
    acb_init(f);
    hecke = flint_malloc(nb_spaces * sizeof(acb_mat_struct));
    source = flint_malloc(nb_spaces * sizeof(acb_mat_struct));
    for (k = 0; k < nb_spaces; k++)
    {
        acb_mat_init(&hecke[k], dims[k], dims[k]);
        acb_mat_init(&source[k], dims[k], dims[k]);
    }

    flint_printf("\n(hecke_attempt) attempt at precision %wd\n", prec);
    hecke_generate_base_points(tau, max_dim, prec);

    flint_printf("(hecke_attempt) evaluating covariants at base points...\n");
    hecke_source(source, nb_spaces, dims, characters, pols_indices, tau, max_dim, ctx, prec);
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        res = acb_mat_inv(&source[k], &source[k], prec);
    }

    flint_printf("(hecke_attempt) evaluating Hecke action...\n");
    for (k = 0; (k < nb) && res; k++)
    {
        if (k % 100 == 0)
        {
            flint_printf("%wd/%wd\n", k, nb);
        }
        hecke_add_term(hecke, nb_spaces, dims, characters, pols_indices, tau, max_dim,
            k, p, is_T1, ctx, prec);
    }

    /* Get rational matrix for each space */
    flint_printf("(hecke_attempt) recognizing matrices...\n");
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        flint_printf("got hecke:\n");
        acb_mat_printd(&hecke[k], 5);

        acb_mat_mul(&hecke[k], &hecke[k], &source[k], prec);
        k0 = ctx->ks[pols_indices[k]];
        if (characters[k])
        {
            k0 += 5;
        }
        j0 = ctx->js[pols_indices[k]];
        hecke_rescale(f, k0, j0, p, is_T1, prec);

        flint_printf("before & after rescaling:\n");
        acb_mat_printd(&hecke[k], 5);
        acb_mat_scalar_mul_acb(&hecke[k], &hecke[k], f, prec);
        acb_mat_printd(&hecke[k], 5);

        flint_printf("(hecke_attempt) found Hecke matrix on space number %wd:\n", k);
        acb_mat_printd(&hecke[k], 5);

        /* Round to integral matrix */
        for (j = 0; (j < dims[k]) && res; j++)
        {
            for (l = 0; (l < dims[k]) && res; l++)
            {
                res = acb_get_approx_fmpq(fmpq_mat_entry(&mats[k], j, l),
                    acb_mat_entry(&hecke[k], j, l), prec);
            }
        }

        if (res)
        {
            fmpq_mat_print(&mats[k]);
        }
    }

    if (res)
    {
        flint_printf("Success!\n");
    }
    else
    {
        flint_printf("Fail at precision %wd, increase precision\n", prec);
    }

    /* Clear and exit */
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_clear(&tau[k]);
    }
    flint_free(tau);
    acb_clear(f);
    for (k = 0; k < nb_spaces; k++)
    {
        acb_mat_clear(&hecke[k]);
        acb_mat_clear(&source[k]);
    }
    flint_free(hecke);
    flint_free(source);
    return res;
}

/* ---------- Main ---------- */

int main(int argc, const char *argv[])
{
    slong q, nb_spaces, p, max_dim;
    int is_T1;
    slong* dims = NULL;
    int* characters = NULL;
    slong prec;
    fmpz_mpoly_vec_t pols;
    slong* pols_indices;
    fmpz_mpoly_ctx_t ctx;
    hecke_mpoly_ctx_t hecke_ctx;
    fmpq_mat_struct* mats;
    FILE* file_out;
    slong k, j;
    int done = 0;

    if (argc != 4)
    {
        flint_printf("Error: expected 3 arguments (p or p^2, filename_in, filename_out), got %wd\n", argc - 1);
        flint_abort();
    }

    flint_printf("(hecke) Call with q = %s, input: %s, output: %s\n", argv[1], argv[2], argv[3]);

    q = strtol(argv[1], NULL, 10);
    parse_integers(&nb_spaces, &dims, &characters, argv[2]);
    if (nb_spaces == 0)
    {
        flint_printf("Error: empty input\n");
        return 0;
    }

    fmpz_mpoly_ctx_init(ctx, ACB_THETA_G2_COV_NB, ORD_LEX);
    pols_indices = flint_malloc((nb_spaces + 1) * sizeof(slong));
    mats = flint_malloc(nb_spaces * sizeof(fmpq_mat_struct));
    pols_indices[0] = 0;

    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_init(&mats[k], dims[k], dims[k]);
        pols_indices[k + 1] = pols_indices[k] + dims[k];
    }
    fmpz_mpoly_vec_init(pols, pols_indices[nb_spaces], ctx);

    parse_covariants(pols, nb_spaces, dims, pols_indices, argv[2], ctx);
    get_p_from_q(&p, &is_T1, q);
    max_dim = 0;
    for (k = 0; k < nb_spaces; k++)
    {
        max_dim = FLINT_MAX(max_dim, dims[k]);
    }

    flint_printf("(hecke) precomputing additions chains...\n");
    hecke_mpoly_ctx_init(hecke_ctx, pols, pols_indices[nb_spaces], ctx);
    flint_printf("(hecke) done\n");

    prec = 500;
    while (!done)
    {
        done = hecke_attempt(mats, nb_spaces, dims, characters, pols_indices,
            max_dim, p, is_T1, hecke_ctx, prec);
        prec *= 2;
    }

    file_out = fopen(argv[3], "w");
    if (file_out == NULL)
    {
        flint_printf("Error: unable to write to file %s\n", argv[3]);
        flint_abort();
    }
    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_fprint_pretty(file_out, &mats[k]);
        fprintf(file_out, "\n\n");
    }
    fclose(file_out);

    fmpz_mpoly_vec_clear(pols, ctx);
    flint_free(pols_indices);
    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_clear(&mats[k]);
    }
    flint_free(mats);
    flint_free(dims);
    flint_free(characters);
    fmpz_mpoly_ctx_clear(ctx);
    hecke_mpoly_ctx_clear(hecke_ctx);

    flint_cleanup();
    return 0;
}
