#include <stdio.h>
#include <stdlib.h>
#include <math.h>

void print_poly(int* p, int len){
    int i;
    for(i=0;i<len;i++){
        if(i!=len-1)printf("%dx^%d + ",p[i],i);
        else printf("%dx^%d",p[i],i);
    }
    printf("\n");
}

int modrev(int num, int mod){           //num^-1 (% mod)
    int matrix[2][2]={{1,0},{0,1}};
    int a=mod;
    int b=num;
    while(b>0){
        int q=a/b;
        int r=a%b;
        a=b;
        b=r;
        int m00=matrix[0][0];
        int m01=matrix[0][1];
        int m10=matrix[1][0];
        int m11=matrix[1][1];
        matrix[0][0]=m10;
        matrix[0][1]=m11;
        matrix[1][0]=m00-q*m10;
        matrix[1][1]=m01-q*m11;
    }
    while(matrix[0][1]<0)matrix[0][1]+=mod;
    return matrix[0][1];
}

void direct_multiply(int* p, int* q, int len, int mod, int* res){
    int i,j;
    for(i=0;i<2*len-1;i++){
        res[i]=0;
        for(j=i;j>=0;j--){
            if(i-j<len && j<len)res[i] += p[j]*q[i-j];
        }
        res[i] %= mod;
    }
}

void karatsuba(int* p, int* q, int len, int mod, int* res){ //iterative
    int d_i[len];
    int c=2*len-3+1;
    int d_st[c/2][c];
    int j;
    for(j=0;j<2*len-1;j++)res[j]=0;
    for(j=0;j<len;j++)d_i[j] = p[j] * q[j] % mod;
    for(j=1;j<c;j++){
        int s=0,t=j;
        while(t>s){
            if(t>=len)d_st[s][t] = p[s]*q[s] % mod;
            else d_st[s][t] = (p[s]+p[t])*(q[s]+q[t]) % mod ;
            s++;
            t--;
        }
    }
    res[0]=d_i[0];
    res[2*len-2]=d_i[len-1];
    for(j=1;j<c;j++){
        int s=0,t=j;
        while(t>s){
            res[j] += d_st[s][t];
            if(t>=len) res[j] -= d_i[s];
            else res[j] -= (d_i[s]+d_i[t]);
            s++;
            t--;
        }
        if(j%2==0)res[j] += d_i[j/2];
        while(res[j]<0)res[j]+=mod;
        res[j]%=mod;
    }
}

void karatsuba_recursive(int* p, int* q, int len, int mod, int* res){
    if(len==1){
        direct_multiply(p,q,len,mod,res);
        return;
    }
    int y=len/2;
    int i;
    int p0[y],p1[y],q0[y],q1[y];
    int z0[len-1],z1[len-1],z2[len-1];
    for(i=0;i<y;i++){
        p0[i]=p[i];
        p1[i]=p[i+y];
        q0[i]=q[i];
        q1[i]=q[i+y];
    }
    karatsuba(p0,q0,y,mod,z0);
    karatsuba(p1,q1,y,mod,z2);
    for(i=0;i<y;i++){
        p0[i]+=p1[i];
        q0[i]+=q1[i];
    }
    karatsuba(p0,q0,y,mod,z1);
    for(i=0;i<2*len-1;i++)res[i]=0;
    for(i=0;i<len-1;i++){
        res[i] += z0[i];
        res[i+y] += (z1[i]-z0[i]-z2[i]);
        res[i+2*y] += z2[i];
    }
    for(i=0;i<2*len-1;i++){
        while(res[i]<0)res[i]+=mod;
        res[i]%=mod;
    }
}

void toom3_karatsuba(int* p, int* q, int len, int mod, int* res){
    int y=len/3;
    int i;
    int p0[y],p1[y],p2[y],q0[y],q1[y],q2[y];
    for(i=0;i<2*len-1;i++)res[i]=0;
    for(i=0;i<y;i++){
        p0[i]=p[i];
        p1[i]=p[i+y];
        p2[i]=p[i+2*y];
        q0[i]=q[i];
        q1[i]=q[i+y];
        q2[i]=q[i+2*y];
    }
    int w_0[2*y-1], w_1[2*y-1], w_neg1[2*y-1], w_neg2[2*y-1], w_inf[2*y-1];
    karatsuba(p0,q0,y,mod,w_0);
    karatsuba(p2,q2,y,mod,w_inf);
    for(i=0;i<y;i++){
        p0[i] += (p1[i]+p2[i]);
        q0[i] += (q1[i]+q2[i]);
    }
    karatsuba(p0,q0,y,mod,w_1);
    for(i=0;i<y;i++){
        p0[i] -= 2*p1[i];
        q0[i] -= 2*q1[i];
    }
    karatsuba(p0,q0,y,mod,w_neg1);
    for(i=0;i<y;i++){
        p0[i] += (3*p2[i]-p1[i]);
        q0[i] += (3*q2[i]-q1[i]);
    }
    karatsuba(p0,q0,y,mod,w_neg2);

    int inv2=modrev(2,mod);
    int inv3=modrev(3,mod);
    int inv6=modrev(6,mod);
    for(i=0;i<2*y-1;i++){
        res[i] += w_0[i];
        res[i+y] += ( inv2*w_0[i] + inv3*w_1[i] - w_neg1[i] + inv6*w_neg2[i] - 2*w_inf[i] ) % mod ;
        res[i+2*y] += ( -w_0[i] + inv2*w_1[i] +inv2*w_neg1[i] - w_inf[i] ) % mod ;
        res[i+3*y] += ( -inv2*w_0[i] + inv6*w_1[i] + inv2*w_neg1[i] - inv6*w_neg2[i] + 2*w_inf[i] ) % mod ;
        res[i+4*y] += w_inf[i];
    }
    for(i=0;i<2*len-1;i++){
        while(res[i]<0)res[i]+=mod;
        res[i] %= mod;
    }
}

int main()
{
    int len = 48;
    int mod = 4591;

    int i;
    int p[len],q[len];
    int res[2*len-1];
    for(i=0;i<len;i++){
        p[i] = (i+1)%mod;
        q[i] = (i+1)%mod;
    }
    printf("\np(x) = ");
    print_poly(p,len);
    printf("\nq(x) = ");
    print_poly(q,len);
    printf("\np(x)*q(x) = ");
    karatsuba(p,q,len,mod,res);
    //direct_multiply(p,q,len,mod,res);
    print_poly(res,2*len-1);
    return 0;
}
