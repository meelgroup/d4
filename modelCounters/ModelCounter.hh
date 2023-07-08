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
#include <unordered_set>

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
     Call the CNF formula into a D-FPiBDD.

     @param[in] setOfVar, the current set of considered variables
     @param[in] unitsLit, the set of unit literal detected at this level
     @param[in] freeVariable, the variables which become free
     @param[in] priority, select in priority these variable to the next decision node

     \return a compiled formula (fpibdd or fbdd w.r.t. the options selected).
  */
  T computeNbModel_(vec<Var> &setOfVar, vec<Lit> &unitsLit, vec<Var> &freeVariable, vec<Var> &priorityVar)
  {
    showRun(); nbCallCall++;
    s.rebuildWithConnectedComponent(setOfVar);

    if(!s.solveWithAssumptions()) return 0;
    s.collectUnit(setOfVar, unitsLit); // collect unit literals

    occManager->preUpdate(unitsLit);

    // compute the connected composant
    vec<Var> reallyPresent;
    vec< vec<Var> > varConnected;
    int nbComponent = occManager->computeConnectedComponent(varConnected, setOfVar, freeVariable, reallyPresent);
    cout << "nbComponent: " << nbComponent << endl;
    cout << "The stat of components: ";
    int nrvars = 0;
    for(int cp = 0 ; cp<nbComponent ; cp++) {
      nrvars += varConnected[cp].size();
    }
    int thresh = nrvars / 2;
    unordered_set<int> first_par;
    int ubound = varConnected.size();
    while (thresh > 0)
    {
      int max_con = 0;
      int max_index = 0;
      for (int cp = 0 ; cp<ubound ; cp++) {
        if (first_par.find(cp) == first_par.end()) {
          if (varConnected[cp].size() > max_con) {
            max_con = varConnected[cp].size();
            max_index = cp;
          }
        }
      }
      thresh = thresh - max_con;
      // swap the index
      // vec<Var> &connected = varConnected[max_index];
      // varConnected[max_index] = varConnected[ubound - 1];
      // varConnected[ubound - 1] = connected;
      // ubound--;
      first_par.insert(max_index);
    }
    int first_half = 0;
    T n1 =0, n2= 0;
    vec<Var> first;
    vec<Var> second;
    for (int cp = 0 ; cp<nbComponent ; cp++) {
      if (first_par.find(cp) == first_par.end()) {
        for (int i = 0; i < varConnected[cp].size(); i++) {
          first.push(varConnected[cp][i]);
        }
      } else {
        for (int i = 0; i < varConnected[cp].size(); i++) {
          second.push(varConnected[cp][i]);
        }
      }
    }
    cout << "First half: " << first.size() << " and second half: " << second.size() << endl;
    vec<Var> idxClauses;
    T ret = 1, curr;
    if(nbComponent)
      {
        nbSplit += (nbComponent > 1) ? nbComponent : 0;
        for(int cp = 0 ; cp<nbComponent ; cp++)
          {
            vec<Var> &connected = varConnected[cp];
            cout << connected.size() << " ";
            // to disable the counting 
            // bool localCache = optCached;
            
            // idxClauses.clear();
            // occManager->updateCurrentClauseSet(connected);
            // occManager->getCurrentClauses(idxClauses, connected);
            // cout << "Number of clauses: " << idxClauses.size() << " " << endl;
            // idxClauses.clear();

            // TmpEntry<T> cb = localCache ? cache->searchInCache(connected, bm) : NULL_CACHE_ENTRY;

            // if(localCache && cb.defined) ret *= cb.getValue();
            // else
            // {
            //   // recursive call
            //   vec<Var> currPriority;
            //   computePrioritySubSet(connected, priorityVar, currPriority);
            //   ret *= (curr = computeDecisionNode(connected, currPriority));

            //   if(localCache) cache->addInCache(cb, curr);
            // }
            occManager->popPreviousClauseSet();
            // to disable the counting
          }
          std::string aspfile = occManager->computeASPProgram();
          // no need to add the previously computed AS
          occManager->addConditioning(aspfile);
          occManager->addProject(aspfile, first);   // minimal models w.r.t. first set of variables
          n1 = occManager->enumerateAnswerSets(aspfile);
          cout << "nModels1: " << n1 << endl;

          aspfile = occManager->computeASPProgram();
          // no need to add the previously computed AS
          occManager->addConditioning(aspfile);
          occManager->addProject(aspfile, second);  // minimal models w.r.t. second set of variables
          n2 = occManager->enumerateAnswerSets(aspfile);
          cout << "nModels2: " << n2 << endl;

      }// else we have a tautology
      cout << endl;

    occManager->postUpdate(unitsLit);
    return n1 * n2;
  }// computeNbModel_

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
    cout << "The variables in cut: ";
    for(int i = 0 ; i<s.nVars() ; i++) {
      if (vs->isProjected(i)) {
        // copying the projection variables
        priorityVar.push(i);
        cout << i+1 << " ";
      }
    }
    cout << endl;
    occManager->preComputedAS.clear();
    for (int as = 0; as < 3; as++) {
      std::string aspfile = occManager->computeASPProgram();
      vector<int> answerset = occManager->computeAnswerSet(aspfile);
      // special for track1_009.cnf (cut is no longer needed)
      // vector<int> cut{225,240,271,286,600,630,727,741,866,871,986,991,1339,1354,1383,1583,1584,1588,1767,1776,1783,2254,2269,2383,2611,2641,2827,2842,2883,2898,2942,3061,3137,3152,3353,3363,3370,3536,3545,3552,4210,4240,4428,4443,4484,4515,4530,4574,4695,4771,4974,4984,4991,5170,5179,5186,5842,5874,6061,6077,6119};
    
      if (answerset.size() == 0) {
        cout << "Found UNSAT !!!";
        break;
      }
      
      vector<std::string> com;
      com.clear();
      int number_of_push = 0;
      for(int i = 0 ; i<priorityVar.size() ; i++) {
        if (find(answerset.begin(), answerset.end(), priorityVar[i]) != answerset.end()) {
          (s.assumptions).push(mkLit(priorityVar[i], false));
          number_of_push++;
          com.push_back("v"+to_string(priorityVar[i]));
        }
        else if (s.value(priorityVar[i]) == l_Undef) {
          (s.assumptions).push(mkLit(priorityVar[i], true));
          number_of_push++;
          com.push_back("not v"+to_string(priorityVar[i]));
          // check whether the logic is correct
        }
      }
      occManager->preComputedAS.push_back(com);
    // for (int n: answerset) {
    //   if (find(answerset.begin(), answerset.end(), n) == answerset.end()) {
    //     // the atom is negative
    //     (s.assumptions).push(~mkLit(n));
    //   } else {
    //     (s.assumptions).push(mkLit(n));
    //   }
    // }
      T d = computeNbModel_(setOfVar, unitsLit, freeVariable, priorityVar);
      cout << "Conditioning on " << as << ": models " << d << endl;
      while (number_of_push > 0) {
        number_of_push--;
        (s.assumptions).pop();
      }
      (s.cancelUntil)((s.assumptions).size());
    }

    if(verb) printFinalStatsCache();

    T computeWeight = 1;
    for(int i = 0 ; i<freeVariable.size() ; i++)
      if(vs->isProjected(freeVariable[i])) computeWeight *= T(weightVar[freeVariable[i]]);
    for(int i = 0 ; i<unitsLit.size() ; i++)
      if(vs->isProjected(var(unitsLit[i]))) computeWeight *= T(weightLit[toInt(unitsLit[i])]);

    return computeWeight;
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
