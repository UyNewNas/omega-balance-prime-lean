// Independent full-range audit. No smallest-prime-factor recurrence is used.
// Primality is Eratosthenes; Omega is accumulated over ALL prime powers.
// Confirms the complete balanced-prime list and every positive witness.
// Missing cases are exhaustively retried; the Python bitset audit also checks <=10^6.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
int main(int argc,char**argv){try{
 if(argc!=3)throw std::runtime_error("usage: verify_witnesses_independent LIMIT PREFIX");
 int L=std::stoi(argv[1]),M=L+1;std::string prefix=argv[2];
 if(L<10||L>200000000||L%2)throw std::runtime_error("invalid limit");
 std::vector<unsigned char> prime(M+1,1),omega(M+1,0),bal(M+1,0);
 prime[0]=prime[1]=0;
 for(int p=2;1LL*p*p<=M;++p)if(prime[p])for(std::int64_t n=1LL*p*p;n<=M;n+=p)prime[n]=0;
 for(int p=2;p<=M;++p)if(prime[p]){
  for(std::int64_t power=p;power<=M;){
   for(std::int64_t n=power;n<=M;n+=power)++omega[n];
   if(power>M/p)break;power*=p;
  }
 }
 std::vector<int>B;
 for(int p=3;p<=L;p+=2)if(prime[p]&&omega[p-1]==omega[p+1]){B.push_back(p);bal[p]=1;}
 std::ifstream bfile(prefix+"_balanced_primes.txt");if(!bfile)throw std::runtime_error("missing primes file");
 std::string header;std::getline(bfile,header);int q;
 for(int p:B){if(!(bfile>>q)||q!=p)throw std::runtime_error("balanced list mismatch");}
 if(bfile>>q)throw std::runtime_error("extra balanced list entry");
 std::ifstream wfile(prefix+"_witnesses.bin",std::ios::binary);if(!wfile)throw std::runtime_error("missing witnesses");
 std::ifstream efile(prefix+"_missing.txt");if(!efile)throw std::runtime_error("missing exceptions");std::getline(efile,header);
 std::vector<std::uint32_t>buffer(1<<18);int n=2,missing=0,last=0,diagonal_only=0;
 while(wfile){
  wfile.read(reinterpret_cast<char*>(buffer.data()),buffer.size()*4);auto bytes=wfile.gcount();
  if(bytes%4)throw std::runtime_error("truncated witness record");
  for(std::streamsize i=0;i<bytes/4;++i,n+=2){
   if(n>L)throw std::runtime_error("extra witness record");
   auto p=buffer[i];
   if(p){
    if(p>unsigned(n/2)||!bal[p]||!bal[n-p])throw std::runtime_error("invalid positive witness at "+std::to_string(n));
    if(p==unsigned(n/2)){
     bool earlier=false;for(int z:B){if(z>=int(p))break;if(bal[n-z]){earlier=true;break;}}
     if(earlier)throw std::runtime_error("witness not minimal at diagonal case");
     ++diagonal_only;
    }
   }else{
    ++missing;last=n;
    if(!(efile>>q)||q!=n)throw std::runtime_error("exceptions mismatch");
    for(int z:B){if(z>n/2)break;if(bal[n-z])throw std::runtime_error("false missing at "+std::to_string(n));}
   }
  }
 }
 if(n!=L+2||efile>>q)throw std::runtime_error("incomplete report");
 std::cout<<"PASS: independent bound="<<L<<"; balanced_primes="<<B.size()<<"; verified_even_targets="<<L/2<<"; missing="<<missing<<"; largest_missing="<<last<<"; diagonal_only="<<diagonal_only<<"\n";
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
