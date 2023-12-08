/*
* d4
* Copyright (C) 2020  Univ. Artois & CNRS
* 
* This program is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* (at your option) any later version.
* 
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
* 
* You should have received a copy of the GNU General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
#ifndef MODELCOUNTERS_MODELCOUNTER_h
#define MODELCOUNTERS_MODELCOUNTER_h

#include <iostream>
#include <fstream>
#include <errno.h>
#include <cstring>

#include <signal.h>
#include <zlib.h>

#include "../interfaces/BucketManagerInterface.hh"
#include "../interfaces/OccurrenceManagerInterface.hh"
#include "../interfaces/PartitionerInterface.hh"
#include "../interfaces/VariableHeuristicInterface.hh"

#include "../manager/dynamicOccurrenceManager.hh"
#include "../manager/BucketManager.hh"
#include "../manager/CacheCNFManager.hh"

#include "../utils/System.hh"
#include "../utils/SolverTypes.hh"
#include "../utils/Dimacs.hh"
#include "../utils/Solver.hh"
#include "../utils/equiv.hh"

#include "../mtl/Sort.hh"
#include "../mtl/Vec.hh"
#include "../mtl/Heap.hh"
#include "../mtl/Alg.hh"

#include "../manager/OptionManager.hh"
#include "../core/ShareStructures.hh"

#define NB_SEP_MC 129
#define MASK_SHOWRUN_MC ((2<<13) - 1)

#include <boost/multiprecision/gmp.hpp>
using namespace boost::multiprecision;


using namespace std;


template <class T> class ModelCounter
{
private:
  // statistics
  int nbNodeInCall;
  int nbCallCall;
  int nbSplit;
  int callEquiv, callPartitioner;
  double currentTime;

  unsigned int nbDecisionNode;
  CacheCNF<T> *cache;

  vec<unsigned> stampVar;
  unsigned stampIdx;

  int freqLimitDyn;
  int optCached;
  bool optDomConst;
  bool optReversePolarity;

  VariableHeuristicInterface *vs;
  PartitionerInterface *pv;

  BucketManagerInterface<T> *bm;
  EquivManager em;

  Solver s;
  vec<double> weightLit, weightVar;
  OccurrenceManagerInterface *occManager;
  vec<vec<Lit> > clauses;

  int limitCacheDyn;
  TmpEntry<T> NULL_CACHE_ENTRY;

  /**
     Compute the current priority set.
   */
  inline void computePrioritySubSet(vec<Var> &connected, vec<Var> &priorityVar, vec<Var> &currPriority)
  {
    currPriority.clear();
    stampIdx++;
    for(int i = 0 ; i<connected.size() ; i++) stampVar[connected[i]] = stampIdx;
    for(int i = 0 ; i<priorityVar.size() ; i++)
      if(stampVar[priorityVar[i]] == stampIdx && s.value(priorityVar[i]) == l_Undef)
        currPriority.push(priorityVar[i]);
  } // computePrioritySet

  /**
     Check the current priority set.
   */
  inline bool hasPriorityVariables(vec<Var> &connected, vec<Var> &priorityVar)
  {
    stampIdx++;
    for(int i = 0 ; i<connected.size() ; i++) stampVar[connected[i]] = stampIdx;
    for(int i = 0 ; i<priorityVar.size() ; i++)
      if(stampVar[priorityVar[i]] == stampIdx && s.value(priorityVar[i]) == l_Undef)
        return true; // there are intersections

    return false;
  } // hasPriorityVariables


  /**
     Call the CNF formula into a D-FPiBDD.

     @param[in] setOfVar, the current set of considered variables
     @param[in] unitsLit, the set of unit literal detected at this level
     @param[in] freeVariable, the variables which become free
     @param[in] priority, select in priority these variable to the next decision node

     \return a compiled formula (fpibdd or fbdd w.r.t. the options selected).
  */
  T computeNbModel_(vec<Var> &setOfVar, vec<Lit> &unitsLit, vec<Var> &freeVariable, vec<Var> &priorityVar)
  {
    // disable the output
    // showRun(); nbCallCall++;
    s.rebuildWithConnectedComponent(setOfVar);

    if(!s.solveWithAssumptions()) return 0;
    s.collectUnit(setOfVar, unitsLit); // collect unit literals

    occManager->preUpdate(unitsLit);

    // compute the connected composant
    vec<Var> reallyPresent;
    vec< vec<Var> > varConnected;
    int nbComponent = occManager->computeConnectedComponent(varConnected, setOfVar, freeVariable, reallyPresent);
    // bool earlyReject = true;
    // if (earlyReject) {
    //   bool hasIntersection = true;
    //   for(int cp = 0 ; cp<nbComponent ; cp++) {
    //     vec<Var> &connected = varConnected[cp];
    //     hasIntersection &= hasPriorityVariables(connected, priorityVar);
    //   }
    //   if (!hasIntersection) {
    //     occManager->postUpdate(unitsLit); // I think it should be there
    //     return 0; // the number of stable models is 0
    //   }
    // }
    T ret = 1, curr;
    if(nbComponent)
      {
        nbSplit += (nbComponent > 1) ? nbComponent : 0;
        for(int cp = 0 ; cp<nbComponent ; cp++)
          {
            vec<Var> &connected = varConnected[cp];
            bool localCache = optCached;

            occManager->updateCurrentClauseSet(connected);
            TmpEntry<T> cb = localCache ? cache->searchInCache(connected, bm) : NULL_CACHE_ENTRY;

            if(localCache && cb.defined) ret *= cb.getValue();
            else
            {
              // recursive call
              vec<Var> currPriority;
              computePrioritySubSet(connected, priorityVar, currPriority);
              ret *= (curr = computeDecisionNode(connected, currPriority));

              if(localCache) cache->addInCache(cb, curr);
            }
            occManager->popPreviousClauseSet();
          }
      }// else we have a tautology

    occManager->postUpdate(unitsLit);
    return ret;
  }// computeNbModel_

  unsigned callBaselineSolver(string aspfile) {
    // running clingo to compute minimal models
    string clingo_cmd = "clingo ";
    system(string(clingo_cmd + " -q -n 0 -W none " + aspfile + "> result_" + aspfile).c_str());
    ifstream resultfile("result_" + aspfile);
    string line; 
    bool solutionFound = false;
    unsigned nSoln = 0;
    while (getline (resultfile, line)) {
      if (line.find("Models") == 0) {
        solutionFound = true;
        size_t pos = 0;
        std::string token;
        std::string delimiter = ":";
        pos = line.find(delimiter);
        token = line.substr(pos + delimiter.length(), line.length());
        nSoln = stoul(token);
      }
    }
    if (solutionFound) {
      return nSoln;
    }
    cout << "Cannot find solutions " << endl;
    return nSoln;
  }

  /**
     This function select a variable and compile a decision node.

     @param[in] connected, the set of variable present in the current problem
     \return the compiled formula
  */
  T computeDecisionNode(vec<Var> &connected, vec<Var> &priorityVar)
  {
    if(pv && !priorityVar.size() && connected.size() > 10 && connected.size() < 5000)
      {
        vec<int> cutSet;
        pv->computePartition(connected, cutSet, priorityVar, vs->getScoringFunction());
        callPartitioner++;
      }

    Var v = var_Undef;
    // this is important for stable model counting
    // if (priorityVar.size() == 0) {
    //   return 0
    // }
    if(priorityVar.size()) v = vs->selectVariable(priorityVar); else v = vs->selectVariable(connected);
    // cout << "priorityVar.size(): " << priorityVar.size() << endl;
    // for (int i = 0; i < priorityVar.size() ; i++) {
    //   cout << priorityVar[i] << " ";
    // }
    vec<Var> nonCopyVar, copyVar;
    vec< vec<Lit> > relClauses;
    int nCls = 0;
    string rule_str = "";
    int thresh = 40;
    bool hasSmallModels = occManager->checkHeuristics(priorityVar, thresh);
    if (hasSmallModels) {
      ofstream myfile;
      string aspfile = "asp.lp";
      myfile.open(aspfile);
      nCls = occManager->computeRelevantClauses(connected, relClauses, copyVar, nonCopyVar);
      // cout << "Number of clauses in residual formula: " << nCls << endl;
      cout << "The rules of residual program: (" << nCls << ")" << endl;
      vec<Var> pos_lit, neg_lit;
      for(int cp = 0 ; cp < nCls ; cp++) {
        vec<Lit> &c = relClauses[cp];
        pos_lit.clear();
        neg_lit.clear();
        for (int in = 0; in < c.size(); in++) {
          if (sign(c[in])) {
            neg_lit.push(var(c[in]));
          } else {
            pos_lit.push(var(c[in]));
          }
        }
        rule_str = "";
        for (int lit_in = 0; lit_in < pos_lit.size(); lit_in++) {
          rule_str += ("v" + to_string(pos_lit[lit_in]));
          if (lit_in < pos_lit.size() - 1) {
            rule_str += ";";
          }
        }
        rule_str += ":-";
        for (int lit_in = 0; lit_in < neg_lit.size(); lit_in++) {
          rule_str += ("v" + to_string(neg_lit[lit_in]));
          if (lit_in < neg_lit.size() - 1) {
            rule_str += ",";
          }
        }
        rule_str += ".";
        myfile << rule_str << endl;
      }
      unordered_map<Var, bool> priorityVarPresent;
      // cout << "The projection variables: (" << priorityVar.size() << ")" << endl;
      for (int pv = 0 ; pv<priorityVar.size() ; pv++) {
        // cout << readableVar(priorityVar[pv]) << " ";
        assert(priorityVar[pv] >= 0);
        priorityVarPresent[priorityVar[pv] + s.nVars() / 2] = true;
        // it should be +1
      }
      // cout << "The conditionals: " << endl;
      for (int pv = 0 ; pv<connected.size() ; pv++) {
        Var v = connected[pv];
        rule_str = "";
        if (readableVar(v) > s.nVars() / 2 && priorityVarPresent.find(v) == priorityVarPresent.end()) {
          rule_str += ":- not " + ("v" + to_string(v)) + ".";
          myfile << rule_str << endl;
        }
      }
      // calling the baseline solver to enumerate minimal models
      T nSoln = callBaselineSolver(aspfile);
      return nSoln;
    }

    // if(priorityVar.size() == 0 && connected.size() > 0) {
    //   // it is the special base cases
    //   return 0;
    // }
    if(v == var_Undef) return 1; 

    Lit l = mkLit(v, optReversePolarity - vs->selectPhase(v));
    nbDecisionNode++;

    // compile the formula where l is assigned to true
    vec<Lit> unitLitPos, unitLitNeg;
    vec<Var> freeVarPos, freeVarNeg;

    (s.assumptions).push(l);
    T pos = computeNbModel_(connected, unitLitPos, freeVarPos, priorityVar);
    pos *= computeWeightUnitFree(unitLitPos, freeVarPos);
    (s.assumptions).pop();
    (s.cancelUntil)((s.assumptions).size());

    (s.assumptions).push(~l);
    T neg = computeNbModel_(connected, unitLitNeg, freeVarNeg, priorityVar);
    neg *= computeWeightUnitFree(unitLitNeg, freeVarNeg);
    (s.assumptions).pop();
    (s.cancelUntil)((s.assumptions).size());

    return neg + pos;
  }// computeDecisionNode


  inline void showHeader()
  {
    separator();
    fprintf(stderr, "c %10s | %10s | %10s | %10s | %10s | %10s | %10s | %10s | %11s | %10s |\n",
           "#compile", "time", "#posHit", "#negHit", "#split",
            "Mem(MB)", "#equivCall", "#Dec. Node", "#partioner", "limitDyn");
    separator();
  }


  inline void showInter()
  {
    double now = cpuTime();

    printf("c %10d | %10.2lf | %10d | %10d | %10d | %10.0lf | %10d | %10d | %11d | %10d |\n",
           nbCallCall, now - currentTime, cache->getNbPositiveHit(),
           cache->getNbNegativeHit(), nbSplit, memUsedPeak(),
           callEquiv, nbDecisionNode, callPartitioner, limitCacheDyn);
  }

  inline void showRun()
  {
    if(!(nbCallCall & (MASK_HEADER))) showHeader();
    if(nbCallCall && !(nbCallCall & MASK_SHOWRUN_MC)) showInter();
  }

  inline void separator(){ printf("c "); for(int i = 0 ; i<NB_SEP_MC ; i++) printf("-"); printf("\n");}


  inline void init(int nbClauses, int maxSizeClause, vec<double> &wl, OptionManager &optList,
                   vec<bool> &isProjectedVar)
  {
    wl.copyTo(weightLit);
    for(int i = 0 ; i<wl.size()>>1 ; i++) s.newVar();
    for(int i = 0 ; i<s.nVars() ; i++)
    {
      weightVar.push(weightLit[i<<1] + weightLit[(i<<1) | 1]);
    }
    limitCacheDyn = s.nVars();

    callPartitioner = callEquiv = 0;
    optCached = optList.optCache;
    optReversePolarity = optList.reversePolarity;

    optList.printOptions();

    // initialized the data structure
    prepareVecClauses(clauses, s);
    occManager = new DynamicOccurrenceManager(0, s.nVars(), 0);

    cache = new CacheCNF<T>(optList.reduceCache, optList.strategyRedCache);
    cache->initHashTable(occManager->getNbVariable(), nbClauses, maxSizeClause);

    vs = new VariableHeuristicInterface(s, occManager, optList.varHeuristic,
                                        optList.phaseHeuristic, isProjectedVar);
    bm = new BucketManager<T>(occManager, nbClauses, s.nVars(), maxSizeClause, optList.strategyRedCache);
    pv = PartitionerInterface::getPartitioner(s, occManager, optList);
    bm->setFixeFormula(optList.cacheStore);

    // statistics initialization
    nbSplit = nbCallCall = 0;
    currentTime = cpuTime();
    nbDecisionNode = nbNodeInCall = 0;

    stampIdx = 0;
    stampVar.initialize(s.nVars(), 0);
    em.initEquivManager(s.nVars());
  }// init

public:

  T getWeightVar(Var v){return T(weightVar[v]);}

  /**
     Compute the value for free and unit variables.

     @param[in] units, the units variables
     @param[in] frees, the free variables

     \return the right value
   */
  inline T computeWeightUnitFree(vec<Lit> &units, vec<Var> &frees)
  {
    T tmp = 1;
    for(int i = 0 ; i<units.size() ; i++)
      if(vs->isProjected(var(units[i]))) tmp *= T(weightLit[toInt(units[i])]);
    for(int i = 0 ; i<frees.size() ; i++)
      if(vs->isProjected(frees[i])) tmp *= T(weightVar[frees[i]]);
    return tmp;
  } // computeValue


  inline void printFinalStatsCache()
  {
    separator();
    printf("c\n");
    printf("c \033[1m\033[31mStatistics \033[0m\n");
    printf("c \033[33mCompilation Information\033[0m\n");
    printf("c Number of recursive call: %d\n", nbCallCall);
    printf("c Number of split formula: %d\n", nbSplit);
    printf("c Number of decision: %u\n", nbDecisionNode);
    printf("c Number of paritioner calls: %u\n", callPartitioner);
    printf("c \n");
    cache->printCacheInformation();
    printf("c Final time: %lf\n", cpuTime());
    printf("c \n");
  } // printFinalStat


  /**
     Constructor of model counter that does not take a formula as
     input (the formula is given later).

     @param[in] fWeights, the vector of literal's weight
     @param[in] optList, the options
     @param[in] isProjectedVar, boolean vector used to decide if a variable is projected (true) or not (false)
  */
  ModelCounter(int nbClauses, int maxSizeClause, vec<double> &wl, OptionManager &optList,
               vec<bool> &isProjectedVar)
  {
    init(nbClauses, maxSizeClause, wl, optList, isProjectedVar);
  } // ModelCounter


  /**
     Constructor of model counter.

     @param[in] cnf, set of clauses
     @param[in] fWeights, the vector of literal's weight
     @param[in] optList, the options
     @param[in] isProjectedVar, boolean vector used to decide if a variable is projected (true) or not (false)
  */
  ModelCounter(vec<vec<Lit> > &cnf, vec<double> &wl, OptionManager &optList, vec<bool> &isProjectedVar)
  {
    // init the model counter's date structures
    int maxSizeClause = 0;
    for(int i = 0 ; i<cnf.size() ; i++) if(cnf[i].size() > maxSizeClause) maxSizeClause = cnf[i].size();
    init(cnf.size(), maxSizeClause, wl, optList, isProjectedVar);

    // init the solver
    for(int i = 0 ; i<cnf.size() ; i++) s.addClause_(cnf[i]);

    // test the satifiability of the input formula
    if(!s.solveWithAssumptions()){printf("c The formula is unsatisfiable\ns 0\n"); exit(0);}
    s.simplify();
    s.remove_satisfied = false;
    s.setNeedModel(false);

    // add the clauses to the occurrence manager
    vec<vec<Lit> > reduceCnf;
    for(int i = 0 ; i<cnf.size() ; i++)
    {
      bool isSAT = false;
      reduceCnf.push();
      vec<Lit> &cl = cnf[i], &redCl = reduceCnf.last();

      for(int j = 0 ; !isSAT && j<cl.size() ; j++)
      {
        if(s.value(cl[j]) == l_Undef) redCl.push(cl[j]);
        isSAT = isSAT || s.value(cl[j]) == l_True;
      }


      if(isSAT) reduceCnf.pop();
      else assert(redCl.size());
    }

    freqLimitDyn = optList.freqLimitDyn;
    occManager->initFormula(reduceCnf);
    cache->setInfoFormula(s.nVars(), reduceCnf.size(), occManager->getMaxSizeClause());
  }// ModelCounter

  ~ModelCounter()
  {
    if(pv) delete pv;
    delete cache; delete vs; delete bm;
    delete occManager;
  }

  /**
     Initialize the assumption in order to compute the number of model
     under this one.

     @param[in] assums, the assumption
   */
  void initAssumption(vec<Lit> &assums)
  {
    s.cancelUntil(0);
    assums.copyTo(s.assumptions);
  }// initAssumption


  /**
     Compute the number of model using the trace of a SAT solver.

     \return the number of models
  */
  T computeNbModel(bool verb = true)
  {
    vec<Var> freeVariable, setOfVar, priorityVar;
    vec<Lit> unitsLit;

    for(int i = 0 ; i<s.nVars() ; i++) setOfVar.push(i);
    cout << "The set of projection variables is: ";
    for(int i = 0 ; i<s.nVars() ; i++) {
      if (vs->isProjected(i)) {
        // copying the projection variables
        priorityVar.push(i);
        // for projection var v the corresponding copy var is v + s.nVars() / 2
        cout << "Projection var: " << i+1 << " and copy var " << (i+1) + s.nVars() / 2 << endl;
      }
    }
    cout << endl;
    T d = computeNbModel_(setOfVar, unitsLit, freeVariable, priorityVar);

    if(verb) printFinalStatsCache();

    T computeWeight = 1;
    for(int i = 0 ; i<freeVariable.size() ; i++)
      if(vs->isProjected(freeVariable[i])) computeWeight *= T(weightVar[freeVariable[i]]);
    for(int i = 0 ; i<unitsLit.size() ; i++)
      if(vs->isProjected(var(unitsLit[i]))) computeWeight *= T(weightLit[toInt(unitsLit[i])]);

    return d * computeWeight;
  }// computeNbModel


  /**
     Compute the number of model using the trace of a SAT solver.

     \return the number of models
  */
  T computeNbModel(vec<Var> &setOfVar, bool verb = true)
  {
    vec<Var> freeVariable, priorityVar;
    vec<Lit> unitsLit;

    // we need to collect the variabels they are in the assumption and not in setOfVar
    vec<Lit> assumsLit;
    vec<bool> markedVar;

    for(int i = 0 ; i<s.nVars() ; i++) markedVar.push(false);
    for(int i = 0 ; i<setOfVar.size() ; i++) markedVar[setOfVar[i]] = true;
    for(int i = 0 ; i<s.assumptions.size() ; i++)
      if(!markedVar[var(s.assumptions[i])]) assumsLit.push(s.assumptions[i]);

    occManager->preUpdate(assumsLit);
    T d = computeNbModel_(setOfVar, unitsLit, freeVariable, priorityVar);
    occManager->postUpdate(assumsLit);

    if(verb) printFinalStatsCache();

    T computeWeight = 1;
    for(int i = 0 ; i<freeVariable.size() ; i++)
      if(vs->isProjected(freeVariable[i])) computeWeight *= T(weightVar[freeVariable[i]]);
    for(int i = 0 ; i<unitsLit.size() ; i++)
      if(vs->isProjected(var(unitsLit[i]))) computeWeight *= T(weightLit[toInt(unitsLit[i])]);

    return d * computeWeight;
  }// computeNbModel

};

#endif
