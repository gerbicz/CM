// Written by Robert Gerbicz. Free software, sell, resell, use, modify it, whatever you want.

/*****************************************************************************/

#include "gmp-impl.h"
void copy_toplimbs(mpz_ptr a,mpz_ptr b,mp_size_t numlimb){
// copy the top numlimb limbs from b into a (assume that b has at least numlimb limbs)
    MPZ_REALLOC(a,numlimb);
    MPN_COPY(PTR(a),PTR(b)+mpz_size(b)-numlimb,numlimb);
    SIZ(a)=numlimb;
}

mp_size_t gmp_halfgcd(mpz_t a,mpz_t b,mpz_ptr a0,mpz_ptr b0){
// half gcd for (a,b) it is reduced to (a0,b0), its size is the return value
// If half gcd fails, then return=0.
// (We don't destroy a,b.)
    
    mp_size_t talloc;
    mp_size_t matrix_scratch;
    mp_size_t asize=SIZ(a);
    mp_size_t bsize=SIZ(b);
    mp_size_t n=MAX(asize,bsize);
    mp_size_t nn;
    
    mp_ptr ap,bp;
    mp_ptr tp;
    
    TMP_DECL;
    TMP_MARK;

    ap=TMP_ALLOC_LIMBS(n);
    bp=TMP_ALLOC_LIMBS(n);
    MPN_COPY(ap,PTR(a),asize);
    MPN_COPY(bp,PTR(b),bsize);
    if(asize<n)MPN_ZERO(ap+asize,n-asize);
    if(bsize<n)MPN_ZERO(bp+bsize,n-bsize);
    
    matrix_scratch=MPN_HGCD_MATRIX_INIT_ITCH(n);
    talloc=4*n+2+matrix_scratch;// 2*n+2+matrix_scratch was too small, why??
    tp=TMP_ALLOC_LIMBS(talloc);
    MPN_ZERO(tp,2*n+2);

    struct hgcd_matrix M;

    mpn_hgcd_matrix_init(&M,n,tp);
    nn=mpn_hgcd(ap,bp,n,&M,tp+matrix_scratch);

    if(nn!=0){
       MPZ_REALLOC(a0,nn);
       MPZ_REALLOC(b0,nn);
       MPN_COPY(PTR(a0),ap,nn);
       MPN_COPY(PTR(b0),bp,nn);
       SIZ(a0)=nn;
       SIZ(b0)=nn;
    }
    
    TMP_FREE;
    return nn;
}

const int rem8[8]={0,0,0,1,0,1,0,0};
int my_legendre(int_cl_t a,int_cl_t b)
{
       if(b<0) b=-b;
       a%=b;
       if(a<0) a+=b;
       if(a==0)return 0;
       int sym=0;
       int_cl_t c;
       while(a>1) {
               if((a&3)==0)  a>>=2;
               else if((a&3)==2) {
                       sym^=rem8[b&7],a>>=1;
                       if((a&b&3)==3) sym^=1;
                               c=a,a=b,b=c;
                               if(a>=b)  {
                                       a-=b;
                                       if(a>=b)  {
                                          a-=b;
                                            if(a>=b)  {
                                                    a-=b;
                                                    if(a>=b)  {
                                                            a-=b;
                                                            if(a>=b)  {
                                                                    a-=b;
                                                                    if(a>=b)  a%=b;
                                                                       }
                                                              }
                                                      }
                                              }
                                      }
                    }
       else{
             if((a&b&3)==3) sym^=1;
             c=a,a=b,b=c;
             if(a>=b)  {
                     a-=b;
                     if(a>=b)  {
                         a-=b;
                         if(a>=b)  {
                                 a-=b;
                                 if(a>=b)  {
                                         a-=b;
                                         if(a>=b)  {
                                                 a-=b;
                                                 if(a>=b)  {
                                                         a-=b;
                                                         if(a>=b)  {
                                                                 a-=b;
                                                                 if(a>=b)  {
                                                                         a-=b;
                                                                         if(a>=b)  {
                                                                                 a-=b;
                                                                                 if(a>=b)  a%=b;
                                                                                    }
                                                                           }
                                                                   }
                                                           }
                                                   }
                                           }
                                   }
                           }
                   }
               }
     }

    return 1-(sym<<1);
}

bool corn_solve(const int_cl_t D, mpz_ptr p, mpz_t root, mpz_ptr T, mpz_ptr V, bool* hgcd_fail){
// get T,V for that T^2+D*V^2=4*p
// V=NULL is possible, so set it only if V!=NULL
// Assume that p is odd, root^2==-D mod p, 0<root<p, D>0
// D=={0,3} mod 4.
// return value is true iff there is a solution (if p is prime then it is unique for T,V>0).

/*
The classical approach:
let root an integer for that root^2==-D mod (4*p), where 0<root<2*p
    do an Euclidean algorithm (Cornacchia) on u,t=root,2*p and stop when min(u,t)^2<4*p
       then min(u,t) will be the only solution candidate for t in the t^2+d*v^2=4*p equation (for t,v>0).
    for faster algorithm replace the Euclidean with half gcd, and do only a few steps in Euclidean.

This code:
1. Do half gcd with gmp (if fails run Pari code).
2. Do some steps on Euclidean algorithm on the top limbs, this takes constant time(!),
      independent on the size of p, with small probability fails.
3. Check that T^2+D*V^2=4*p mod 8 could be true or not [T is still not computed].
4. Calculate T and check T^2+D*V^2=4*p mod D.
5. V^2=(4*p-T^2)/D so (4*p-T^2)*D is also square, do quadratic residue tests
      for the first few odd primes for (4*p-T^2)*D mod q  [T^2 is still not computed]
6. Calculate (4*p-T^2)/D and check if it is a perfect square and calculate V also if V!=NULL was set.
*/

#define eps 0.000001
// To reach that with approx less than eps probability the Euclidean algorithm fails.
//    too small eps is also wrong, since that gives barely slower code. (eps=1e-6=0.000001 is fine).

    const int ptab[]={3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,0};
    // last zero is a sentinel, odd primes whose product still fits in unsigned 64 bits.
    bool ans=false;
    mpz_t p2,a0,b0,sq,tmp,u,t,q,m00,m01,m10,m11,qres;
    mpz_init(p2);
    mpz_init(a0);
    mpz_init(b0);
    mpz_init(sq);
    mpz_init(tmp);
    mpz_init(u);
    mpz_init(t);
    mpz_init(q);
    mpz_init(m00);
    mpz_init(m01);
    mpz_init(m10);
    mpz_init(m11);
    mpz_init(qres);

    mpz_mul_2exp(p2,p,1);
    
    if(D%2!=(mpz_even_p(root)!=0?0:1)){// D and root has different parity
        mpz_add(root,root,p);
    }
    // with this now root^2==-D mod 4, so root^2==-D mod (4p) is also true.
    
    mp_size_t ret=gmp_halfgcd(root,p2,a0,b0);// p2=2*p
    if(ret==0){
        *hgcd_fail=true;
        goto mydel;
    }
    
    if(mpz_cmp(a0,b0)<0){
        mpz_swap(a0,b0);
    }
    
    mp_size_t limbs=mpz_size(p),limbs2;
    
// we will shift u,t by (limbs+1)/2-g limbs for the Euclidean algorithm
// g=1,2 is good in most of the cases to avoid numerical errors,
// smaller value gives faster code, so select the smallest possible g value

    for(int g=1;;g++){
        
        limbs2=(limbs+1)/2-g;

        if(SIZ(a0)<=limbs2 || SIZ(b0)<=limbs2){
            continue;
        }
        
        if(limbs2<0 || g>=10){
            *hgcd_fail=true;// ok, not gcd failed, but we would copy too much if limbs2<0
            goto mydel;     //     or for g=10: not computed, but g=10 is quite impossible 
        }

        copy_toplimbs(sq,p,limbs-2*limbs2);
        mpz_sqrt(sq,sq);
        mpz_mul_2exp(sq,sq,1);// few toplimbs of 2*sqrtint(p)
    
        copy_toplimbs(u,a0,SIZ(a0)-limbs2);
        copy_toplimbs(t,b0,SIZ(b0)-limbs2);
    
        // t/sq<<sq should hold, so t<eps*sq^2
    
        mpz_pow_ui(tmp,sq,2);
        mpz_fdiv_q_ui(tmp,tmp,1.0>=eps&&eps>0.000000001?(int)1.0/eps:1000000000);
        if(mpz_cmp(t,tmp)<0){
            break;
        }
    }
    
    mpz_set_ui(m00,1);
    mpz_set_ui(m01,0);// u=m00*a0+m01*b0
    mpz_set_ui(m10,0);
    mpz_set_ui(m11,1);// t=m10*a0+m11*b0

    while(mpz_cmp(u,sq)>0&&mpz_cmp(t,sq)>0){
         mpz_fdiv_q(q,u,t);
         mpz_submul(u,t,q);
         
         // u=u-q*t, so for the new u value:
         // m00*a0+m01*b0-q*(m10*a0+m11*b0)=(m00-m10*q)*a0+(m01-m11*q)*b0
         mpz_submul(m00,m10,q);
         mpz_submul(m01,m11,q);

         mpz_swap(u,t);// again u>t
         mpz_swap(m00,m10);
         mpz_swap(m01,m11);
     }
     
     // It will be T=a0*m10+b0*m11
     
     // V^2=={0,1,4} mod 8
     mpz_fdiv_r_2exp(tmp,a0,3); int r0=mpz_get_ui(tmp);
     mpz_fdiv_r_2exp(tmp,m10,3);int r1=mpz_get_ui(tmp);
     mpz_fdiv_r_2exp(tmp,b0,3); int r2=mpz_get_ui(tmp);
     mpz_fdiv_r_2exp(tmp,m11,3);int r3=mpz_get_ui(tmp);
     mpz_fdiv_r_2exp(tmp,p,3);  int r4=4*mpz_get_ui(tmp);
     int r5=D&7;
     int res=(r4-(r0*r1+r2*r3)*(r0*r1+r2*r3))&7;
     if(res!=0 && res!=r5 && res!=((4*r5)&7)){
        // T^2+D*V^2=4*p can not be true mod 8.
        goto mydel;
     }

     // reconstruct the T value. But omit the squaring if we can.
     mpz_mul(a0,a0,m10);
     mpz_addmul(a0,b0,m11);// T=a0

     // check if T^2+D*V^2=4*p mod D is true
     // so if T^2==4*p mod D. (at this point still not computed V)
     r4=mpz_fdiv_r_ui(tmp,p,D);
     mpz_mul_ui(tmp,tmp,4);
     r4=mpz_fdiv_r_ui(tmp,tmp,D);
     
     r0=mpz_fdiv_r_ui(tmp,a0,D);
     mpz_mul(tmp,tmp,tmp);
     mpz_mod_ui(tmp,tmp,D);
     if(mpz_cmp_ui(tmp,r4)!=0){
         // T^2+D*V^2=4*p can not be true mod D.
         goto mydel;
     }

#define prodprimes 16294579238595022365ULL// product of odd primes from 3 to 53, still fits in unsigned 64 bits. approx 2^63.82

     uint_cl_t R0=mpz_fdiv_r_ui(tmp,a0,prodprimes);
     uint_cl_t R1=mpz_fdiv_r_ui(tmp,p,prodprimes);
           
     // if T^2+D*V^2=4*p, then V^2=(4*p-T^2)/D is square, what is the same 
     //       D*(4*p-T^2) is a square, so quadratic residue mod every prime.
     //       check the smallest few (odd) primes.
     
     for(int j=0;ptab[j]!=0;j++){
         int q=ptab[j];
         r0=R0%q;
         r1=(R1%q)<<2;
         r2=D%q;
         r1=((r1-r0*r0)*r2)%q;
         if(r1<0)r1+=q;
         if(my_legendre(r1,q)==-1){
            // not a quadratic residue mod q.
            goto mydel;
          }
      }

      // ok we have to compute the square of T         
      mpz_pow_ui(tmp,a0,2);
      mpz_submul_ui(tmp,p,4);
      mpz_neg(tmp,tmp);
      if(mpz_sgn(tmp)>0){
         mpz_divexact_ui(tmp,tmp,D);// we already know that 4*p-T^2 is divisible by D
               
         if(V==NULL){
            if(mpz_perfect_square_p(tmp)){
               ans=true;
               mpz_set(T,a0);
            }
         }
         else{// V!=NULL case, the value of V is also required, if tmp is a square.
            mpz_sqrtrem(V,qres,tmp);
            if(mpz_sgn(qres)==0){
               ans=true;
               mpz_set(T,a0);
            }
         }
     }
     
     mydel:
        mpz_clear(p2);
        mpz_clear(a0);
        mpz_clear(b0);
        mpz_clear(sq);
        mpz_clear(tmp);
        mpz_clear(u);
        mpz_clear(t);
        mpz_clear(q);
        mpz_clear(m00);
        mpz_clear(m01);
        mpz_clear(m10);
        mpz_clear(m11); 
        mpz_clear(qres);
    
    return ans;   
}

bool cm_pari_cornacchia (mpz_ptr t, mpz_ptr v, mpz_srcptr p,
   mpz_srcptr root, const int_cl_t d)
   /* The function has the same interface as cm_nt_mpz_cornacchia. As PARI
      uses a half gcd, it should be asymptotically faster. */
{
#define limit_gmp_hgcd 512 // For p<2^limit_gmp_hgcd use the original Pari code.
   
   bool ans=false,fail=false;
   mpz_t root2;
   
   mpz_init(root2);
   
   if(mpz_sizeinbase(p,2)<=limit_gmp_hgcd){
       fail=true;
   }
   else{
       mpz_set(root2,root);
       ans=corn_solve(-d,p,root2,t,v,&fail);// if gmp's half gcd code fails it does not mean that there would be no solution, so check it with pari (also if p is small)
   }
   
   if(fail){

   pari_sp av;
   GEN px, py;
   long res;

   av = avma;
   res = cornacchia2_sqrt (icl_get_Z (-d), mpz_get_Z (p), mpz_get_Z (root),
      &px, &py);
   if (res == 1) {
      Z_get_mpz (t, px);
      if (v != NULL)
         Z_get_mpz (v, py);
      
   }
   avma = av;
      
      ans=(res==1);
   }
   
   mpz_clear(root2);

   return ans;
}

/*****************************************************************************/
