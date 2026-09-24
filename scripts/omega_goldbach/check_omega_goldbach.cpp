// Exact coverage test for sums of two Omega-balanced odd primes.
// Omega counts prime factors WITH multiplicity. No floating-point arithmetic.
// Build: g++ -O3 -std=c++17 check_omega_goldbach.cpp -o check_omega_goldbach
// Run: ./check_omega_goldbach 10000000 /mnt/data/balanced_goldbach/run
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using std::uint32_t;
int main(int argc, char** argv) {
 try {
  const int L = argc > 1 ? std::stoi(argv[1]) : 10000000;
  const std::string prefix = argc > 2 ? argv[2] : "omega_goldbach";
  if (L < 10 || L > 200000000 || L%2) throw std::invalid_argument("even limit in [10,200000000] required");
  const int M=L+1;
  std::vector<uint32_t> spf(M+1);
  std::vector<unsigned char> omega(M+1), bal(M+1);
  std::vector<int> primes, B;
  for(int n=2;n<=M;++n){
    if(!spf[n]) {spf[n]=n;primes.push_back(n);}
    omega[n]=omega[n/spf[n]]+1;
    for(int p:primes){
      const std::uint64_t z=std::uint64_t(n)*p;
      if(z>std::uint64_t(M)||p>int(spf[n]))break;
      spf[z]=p;
    }
  }
  for(int p:primes){if(p>L)break;if(p>2&&omega[p-1]==omega[p+1]){B.push_back(p);bal[p]=1;}}
  std::cerr<<"Sieve complete; bound="<<L<<"; balanced primes="<<B.size()<<"\n";
  std::ofstream bout(prefix+"_balanced_primes.txt"), miss(prefix+"_missing.txt"), wit(prefix+"_witnesses.bin",std::ios::binary);
  if(!bout||!miss||!wit) throw std::runtime_error("cannot open output files");
  bout<<"# all Omega-balanced odd primes p <= "<<L<<"\n";
  for(int p:B)bout<<p<<'\n';
  miss<<"# all even n in [2,"<<L<<"] with no n=p+q, p,q Omega-balanced odd primes; repetition allowed\n";
  std::vector<int> missing, distinct_extra;
  int maxfirst=0, maxfirstn=0, cumulative=0, largestmiss=0;
  const std::vector<int> checkpoints={100,1000,10000,100000,1000000,10000000,100000000,200000000};
  struct Stat {int limit,bs,missing,largest;}; std::vector<Stat> stats;
  std::uint64_t probes=0;
  for(int n=2;n<=L;n+=2){
    uint32_t first=0;
    for(int p:B){
      if(p>n/2)break;
      ++probes;
      if(bal[n-p]){first=p;break;}
    }
    wit.write(reinterpret_cast<const char*>(&first),sizeof(first));
    if(!first){missing.push_back(n);miss<<n<<'\n';++cumulative;largestmiss=n;}
    else {
      if(int(first)>maxfirst){maxfirst=first;maxfirstn=n;}
      if(int(first)*2==n)distinct_extra.push_back(n); // no earlier witness exists
    }
    if(std::find(checkpoints.begin(),checkpoints.end(),n)!=checkpoints.end()||n==L){
      stats.push_back({n,int(std::upper_bound(B.begin(),B.end(),n)-B.begin()),cumulative,largestmiss});
      std::cerr<<"n<="<<n<<" missing="<<cumulative<<" last="<<largestmiss<<"\n";
    }
  }
  std::ofstream report(prefix+"_summary.json");
  report<<"{\n  \"limit\": "<<L<<",\n  \"definition\": \"prime(p) and p>2 and Omega(p-1)=Omega(p+1); multiplicities counted\",\n  \"allow_equal\": true,\n  \"balanced_prime_count\": "<<B.size()<<",\n  \"missing_count\": "<<missing.size()<<",\n  \"largest_missing\": "<<largestmiss<<",\n  \"largest_minimal_summand\": "<<maxfirst<<",\n  \"largest_minimal_summand_target\": "<<maxfirstn<<",\n  \"membership_probes\": "<<probes<<",\n  \"checkpoints\": [";
  for(size_t i=0;i<stats.size();++i){auto s=stats[i];if(i)report<<',';report<<"\n    {\"limit\":"<<s.limit<<",\"balanced_primes\":"<<s.bs<<",\"missing\":"<<s.missing<<",\"largest_missing\":"<<s.largest<<'}';}
  report<<"\n  ],\n  \"extra_missing_if_distinct_required\": [";
  for(size_t i=0;i<distinct_extra.size();++i){if(i)report<<',';report<<distinct_extra[i];}
  report<<"]\n}\n";
  std::cerr<<"DONE. max smallest summand="<<maxfirst<<" at n="<<maxfirstn<<" probes="<<probes<<"\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
}
