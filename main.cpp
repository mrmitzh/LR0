#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <cassert>
#include <unordered_map>
#include <set>
#include <algorithm>
#include <stack>

using GlobalGoto = std::map<std::string, int>;

using AugmentedGrammar = std::map<char,std::vector<std::string>>;
enum OperatorType
{
    SHIFT,REDUCE,ACC
};

struct Operation
{
    OperatorType operatorType;
    int itemId;

    Operation() = default;

    explicit Operation(OperatorType operatorType,int itemId = -1)
            :operatorType(operatorType),itemId(itemId)
    {}
    Operation(const Operation& operation) = default;

    Operation(Operation&& operation) = default;

};
using GotoMap = std::map<int,std::map<char,int>>;
using ActionMap = std::map<int,std::map<char,Operation>>;
using FirstSetMap = std::map<char,std::set<char>>;
using FollowSetMap = std::map<char,std::set<char>>;
using ProductionMap = std::map<std::string,int>;
using ProductionVector = std::vector<std::string>;


struct AugmentedProduction
{
    char lhs;
    std::string rhs;
    AugmentedProduction(char _lhs,std::string _rhs)
            :lhs(_lhs),rhs(std::move(_rhs))
    {

    }
};

class SLRItem
{
private:
    std::vector<AugmentedProduction*> productions;

public:

    std::map<char,int> gotos;
    SLRItem() = default;
    ~SLRItem() = default;

    void Push(AugmentedProduction* p)
    {
        productions.push_back(p);
    }

    int Size()
    {
        return static_cast<int>(productions.size());
    }

    bool Contains(const std::string& production)
    {
        for (auto &it : productions) {
            std::string existing = std::string(1, it->lhs) + "->" + it->rhs;
            if(existing==production)
                return true;
        }
        return false;
    }

    AugmentedProduction* operator[](const int index)
    {
        return productions[index];
    }
};

void load_grammar(AugmentedGrammar& augmentedGrammar,std::vector<SLRItem>& slritems,ProductionMap& productionMap,ProductionVector& productionVector)
{
    std::string production;
    std::string lhs,rhs;
    std::string delim = "->";
    getline(std::cin,lhs);
    lhs += "$";
    augmentedGrammar['\''].push_back(lhs);
    slritems[0].Push(new AugmentedProduction('\'',"@"+lhs));
    std::string str = "\'->" + lhs;
    int productionId = 0;
    productionVector.push_back(str);
    productionMap[str] = productionId++;

    while(true)
    {
        getline(std::cin,production);
        if(production.length()<1)
            return;
        auto pos = production.find(delim);
        assert(pos>=0&&pos<production.length());

        productionVector.push_back(production);
        productionMap[production] = productionId++;

        lhs = production.substr(0,pos);
        rhs = production.substr(pos+delim.length(),std::string::npos);
        augmentedGrammar[lhs[0]].push_back(rhs);
        slritems[0].Push(new AugmentedProduction(lhs[0],"@"+rhs));
    }

}

void add_closure(char lookahead,SLRItem& item,AugmentedGrammar& augmentedGrammar)
{
    // only deal with non-Terminal
    if(!isupper(lookahead))
        return;

    std::string lhs = std::string(1,lookahead);

    for(int i = 0;i<augmentedGrammar[lookahead].size();i++)
    {
        std::string rhs = "@" + augmentedGrammar[lookahead][i];
        std::string temp = lhs;
        temp.append("->");
        temp.append(rhs);
        if(!item.Contains(temp))
        {
            item.Push(new AugmentedProduction(lookahead,rhs));
        }
    }
}

void error()
{
    printf("ERROR\n");
}


void get_SLR_items(std::vector<SLRItem>& slritems,AugmentedGrammar& grammar,int& itemid,GlobalGoto& globalGoto,GotoMap& GOTO,ActionMap& ACTION,
                    FollowSetMap& followSetMap,ProductionMap& productionMap)
{

    printf("I%d:\n", itemid);


    //calculate the closure of the current item
    for(int i = 0;i<slritems[itemid].Size();i++)
    {
        std::string rhs = slritems[itemid][i] -> rhs;
        char lookahead = rhs[rhs.rfind('@')+1];
        add_closure(lookahead,slritems[itemid],grammar);
    }

    char lookahead,lhs;
    std::string rhs;

    for(int i = 0;i<slritems[itemid].Size();i++)
    {


        lhs = slritems[itemid][i]->lhs;
        rhs = slritems[itemid][i]->rhs;


        std::string production = std::string(1,lhs) + "->" + rhs;

        auto pos = rhs.find('@');
        lookahead = rhs[pos+1];

        if(lookahead=='\0')
        {
            auto str = production.substr(0,production.find('@'));
            printf("\t%-20s",&production[0]);
            for(const auto& element:followSetMap[lhs])
            {
                if(ACTION[itemid].find(element)==ACTION[itemid].end())
                {
                    ACTION[itemid].insert(std::make_pair(element,Operation(REDUCE,productionMap[str])));
                    printf("\tReduce(%c)=%d",element,productionMap[str]);
                }
            }
            printf("\n");
            continue;
        }
        if(lookahead=='$'&&productionMap[production]==0)
        {
            ACTION[itemid].insert(std::make_pair(lookahead,Operation(ACC)));
            printf("\t%-20s\tREDUCE %d\n",&production[0],0);
            continue;
        }

        // if there is no goto defined for the current input symbol from this
        // item, assign one.
        if(slritems[itemid].gotos.find(lookahead)==slritems[itemid].gotos.end())
        {
            // if there is a global goto defined for the entire production, use
            // that one instead of creating a new one
            if (globalGoto.find(production) == globalGoto.end()) {
                slritems.emplace_back(); // create new state (item)
                // new right-hand-side is identical with '@' moved one space to the right
                std::string newRhs = rhs;
                auto atpos = static_cast<int>(newRhs.find('@'));
                std::swap(newRhs[atpos], newRhs[atpos+1]);
                // add item and update gotos
                slritems.back().Push(new AugmentedProduction(lhs, newRhs));
                slritems[itemid].gotos[lookahead] = static_cast<int>(slritems.size() - 1);
                globalGoto[production] = static_cast<int>(slritems.size() - 1);
            } else {
                // use existing global item
                slritems[itemid].gotos[lookahead] = globalGoto[production];
            }
            printf("\t%-20s\tgoto(%c)=I%d", &production[0], lookahead, globalGoto[production]);

            if(isupper(lookahead))
            {
                GOTO[itemid].insert(std::make_pair(lookahead,slritems[itemid].gotos[lookahead]));
                printf("\tGOTO(%c)=%d",lookahead,slritems[itemid].gotos[lookahead]);
            }else
            {
                //SHIFT
                if(ACTION[itemid].find(lookahead)==ACTION[itemid].end())
                {
                    ACTION[itemid].insert(std::make_pair(lookahead,Operation(SHIFT,slritems[itemid].gotos[lookahead])));
                    printf("\tSHIFT(%c)=%d", lookahead, slritems[itemid].gotos[lookahead]);
                }
                //REDUCE
                for(const auto& prod:grammar)
                {
                    if(followSetMap[prod.first].find(lookahead)!=followSetMap[prod.first].end())
                    {
                        for(const auto& rightOfProduction:prod.second)
                        {
                            if(ACTION[itemid].find(lookahead)==ACTION[itemid].end())
                            {
                                std::string str = std::string(1,prod.first) + "->" + rightOfProduction;
                                ACTION[itemid].insert(std::make_pair(lookahead,Operation(REDUCE,productionMap[str])));
                                printf("\tREDUCE(%c)=%d",lookahead,productionMap[str]);
                            }
                        }
                    }
                }

            }
            printf("\n");
        } else
        {
            auto at = static_cast<int>(rhs.find('@'));
            std::swap(rhs[at],rhs[at+1]);

            int nextItem = slritems[itemid].gotos[lookahead];
            if(!slritems[nextItem].Contains((std::string(1,lhs)+"->"+rhs)))
            {
                slritems[nextItem].Push(new AugmentedProduction(lhs,rhs));
            }
            std::swap(rhs[at],rhs[at+1]);
            printf("\t%-20s\n", &production[0]);
        }
    }
}




void calculateFistSet(AugmentedGrammar& augmentedGrammar,FirstSetMap& firstSetMap)
{
    bool hasChange = true;
    while(hasChange) {
        hasChange = false;
        for (auto it = augmentedGrammar.rbegin(); it != augmentedGrammar.rend(); it++) {
            char lhs = (*it).first;
            auto firstSize = firstSetMap[lhs].size();
            for (const auto &rightProduction:(*it).second) {
                char firstChOfRightProduct = rightProduction.front();
                if (firstChOfRightProduct != lhs) {
                    if (isupper(firstChOfRightProduct)||firstChOfRightProduct=='\'')
                        std::set_union(firstSetMap[lhs].begin(), firstSetMap[lhs].end(),
                                       firstSetMap[firstChOfRightProduct].begin(),
                                       firstSetMap[firstChOfRightProduct].end(),
                                       std::inserter(firstSetMap[lhs], firstSetMap[lhs].end()));
                    else
                        firstSetMap[lhs].emplace(firstChOfRightProduct);
                }
            }
            auto secondSize = firstSetMap[lhs].size();
            if (secondSize > firstSize)
                hasChange = true;
        }
    }
}

void calculateFollowSet(AugmentedGrammar& augmentedGrammar,FirstSetMap& firstSetMap,FollowSetMap& followSetMap)
{
    bool hasChange = true;
    while(hasChange) {
        hasChange = false;
        for (const auto &leftOfProduction:augmentedGrammar)
        {
            char leftCh = leftOfProduction.first;
            for (const auto &rightOfProduction:leftOfProduction.second)
            {
                for (int i = 0; i < rightOfProduction.length(); i++)
                {
                    char rightCh = rightOfProduction[i];
                    if (isupper(rightCh)) {
                        auto firstSize = followSetMap[rightCh].size();
                        if (i + 1 == rightOfProduction.length())
                            std::set_union(followSetMap[rightCh].begin(), followSetMap[rightCh].end(),
                                           followSetMap[leftCh].begin(),followSetMap[leftCh].end(),
                                            std::inserter(followSetMap[rightCh],followSetMap[rightCh].end()));
                        else
                        {
                            char nextCh = rightOfProduction[i + 1];
                            if (isupper(nextCh)) {
                                std::set_union(followSetMap[rightCh].begin(), followSetMap[rightCh].end(),
                                               firstSetMap[nextCh].begin(), firstSetMap[nextCh].end(),
                                               std::inserter(followSetMap[rightCh], followSetMap[rightCh].end()));
                            } else
                            {
                                followSetMap[rightCh].emplace(nextCh);
                            }
                        }
                        auto afterInsert = followSetMap[rightCh].size();
                        if (afterInsert > firstSize)
                            hasChange = true;
                    }
                }
            }
        }
    }
}


void analyze(const std::string& str,ActionMap& ACTION,GotoMap& GOTO,const ProductionVector& productionVector)
{
    std::stack<int> stateStack;
    stateStack.push(0);
    std::stack<char> symbolStack;
    symbolStack.push('\'');
    int pos = 0;
    while(!stateStack.empty()&&!symbolStack.empty())
    {
        const auto& ret = ACTION[stateStack.top()][str[pos]];
        if(ret.operatorType==SHIFT)
        {
            stateStack.push(ret.itemId);
            symbolStack.push(str[pos]);
            pos++;
            printf("SHIFT %d\n",ret.itemId);
        }else if(ret.operatorType==REDUCE)
        {
            auto string = productionVector[ret.itemId];
            auto delim = std::string("->");
            auto delimPos = string.find(delim);
            auto left = string.substr(0,delimPos);
            auto right = string.substr(delimPos+delim.length(),std::string::npos);
            for(int i = 0;i<right.length();i++)
            {
                stateStack.pop();
                symbolStack.pop();
            }
            stateStack.push(GOTO[stateStack.top()][left[0]]);
            symbolStack.push(left[0]);
            printf("Reduce %d\n",ret.itemId);
        }else if(ret.operatorType==ACC)
        {
            printf("ACC\n");
            return;
        }
    }
    error();
}

int main()
{
    int itemid = -1;
    AugmentedGrammar augmentedGrammar;
    std::vector<SLRItem> slritems = {SLRItem()};
    GotoMap GOTO;
    ActionMap ACTION;
    FirstSetMap firstSetMap;
    FollowSetMap followSetMap;

    ProductionMap  productionMap;
    ProductionVector  productionVector;
    GlobalGoto globalGoto;


    printf("Augmented Grammar\n");
    printf("-----------------\n");
    load_grammar(augmentedGrammar,slritems,productionMap,productionVector);
    printf("\n");


    printf("First Set\n");
    printf("-----------------\n");
    calculateFistSet(augmentedGrammar,firstSetMap);
    for(const auto& temp1:firstSetMap)
    {
        printf("%c:{ ",temp1.first);
        for(const auto& temp2:temp1.second)
            printf("%c ",temp2);
        printf("}\n");
    }


    printf("\n");
    printf("Follow Set\n");
    printf("-----------------\n");
    calculateFollowSet(augmentedGrammar,firstSetMap,followSetMap);
    for(const auto& temp1:followSetMap)
    {
        printf("%c:{ ",temp1.first);
        for(const auto& temp2:temp1.second)
            printf("%c ",temp2);
        printf("}\n");
    }
    printf("\n");
    printf("-------------------\n");

    for(int i = 0;i<productionVector.size();i++)
    {
        std::cout<<i<<": "<<productionVector[i]<<std::endl;
    }
    printf("-------------------\n");

    printf("\n");
    printf("Sets of SLR(1) Items\n");
    printf("-------------------\n");
    while(++itemid<slritems.size())
    {
        get_SLR_items(slritems,augmentedGrammar,itemid,globalGoto,GOTO,ACTION,followSetMap,productionMap);
    }
    printf("\n");

    printf("Enter the string need to analysis and it should be ended with'$'\n");
    
    std::string test;
    std::cin>>test;
    analyze(test,ACTION,GOTO,productionVector);

    return 0;
}