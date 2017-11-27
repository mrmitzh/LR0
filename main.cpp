#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <cassert>
#include <unordered_map>
#include <set>
#include <algorithm>

using AugmentedGrammar = std::map<char,std::vector<std::string>>;
using GotoMap = std::map<std::string,int>;

struct Operation
{
    enum OperatorType
    {
        SHIFT,REDUCE
    } operatorType;
    int itemId;
};

using ActionMap  = std::map<char,Operation>;
using FirstSetMap = std::unordered_map<char,std::set<char>>;
using FollowSetMap = std::unordered_map<char,std::set<char>>;


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

void load_grammar(AugmentedGrammar& augmentedGrammar,std::vector<SLRItem>& slritems)
{
    std::string production;
    std::string lhs,rhs;
    std::string delim = "->";
    getline(std::cin,lhs);
    augmentedGrammar['\''].push_back(lhs);
    slritems[0].Push(new AugmentedProduction('\'',"@"+lhs));

    while(true)
    {
        getline(std::cin,production);
        if(production.length()<1)
            return;
        auto pos = production.find(delim);
        assert(pos>=0&&pos<production.length());

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
        if(!item.Contains(lhs+"->"+rhs))
        {
            item.Push(new AugmentedProduction(lookahead,rhs));
        }
    }
}

void get_SLR_items(std::vector<SLRItem>& slritems,AugmentedGrammar& grammar,int& itemid,GotoMap& GOTO)
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

        lookahead = rhs[rhs.find('@')+1];

        if(lookahead=='\0'){
            printf("\t%-20s\n",&production[0]);
            continue;
        }

        if(slritems[itemid].gotos.find(lookahead)==slritems[itemid].gotos.end())
        {
            if(GOTO.find(production)==GOTO.end())
            {
                slritems.emplace_back(); // create new state (item)

                std::string newRhs = rhs;
                auto at = static_cast<int>(newRhs.find('@'));
                std::swap(newRhs[at],newRhs[at+1]);

                slritems.back().Push(new AugmentedProduction(lhs,newRhs));
                slritems[itemid].gotos[lookahead] = static_cast<int>(slritems.size() - 1);
                GOTO[production] = static_cast<int>(slritems.size() - 1);
            }else
                slritems[itemid].gotos[lookahead] = GOTO[production];
            printf("\t%-20s goto(%c)=I%d\n", &production[0], lookahead, GOTO[production]);

        }else
        {
            //move forward @
            auto at = static_cast<int>(rhs.find('@'));
            std::swap(rhs[at],rhs[at+1]);

            int nextItem = slritems[itemid].gotos[lookahead];
            if (!slritems[nextItem].Contains(std::string(&lhs, 1) + "->" + rhs)) {
                slritems[nextItem].Push(new AugmentedProduction(lhs, rhs));
            }
            std::swap(rhs[at],rhs[at+1]);
            printf("\t%-20s\n",&production[0]);
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
                    if (isupper(firstChOfRightProduct))
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
    while(hasChange)
    {
        hasChange = false;
        for(const auto& leftOfProduction:augmentedGrammar)
        {
            for(const auto& rightOfProduction:leftOfProduction.second)
            {
                for(int i = 0;i<rightOfProduction.length();i++)
                {
                    char rightCh = rightOfProduction[i];
                    if(isupper(rightCh))
                    {
                        auto firstSize = followSetMap[rightCh].size();
                        if(i+1==rightOfProduction.length())
                            followSetMap[rightCh].emplace('$');
                        else
                        {
                            char nextCh = rightOfProduction[i+1];
                            if(isupper(nextCh))
                            {
                                std::set_union(followSetMap[rightCh].begin(),followSetMap[rightCh].end(),
                                               firstSetMap[nextCh].begin(),firstSetMap[nextCh].end(),
                                               std::inserter(followSetMap[rightCh],followSetMap[rightCh].end()));
                            }else
                            {
                                followSetMap[rightCh].emplace(nextCh);
                            }
                        }
                        auto afterInsert = followSetMap[rightCh].size();
                        if(afterInsert>firstSize)
                            hasChange = true;
                    }
                }
            }
        }
    }

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

    printf("Augmented Grammar\n");
    printf("-----------------\n");
    load_grammar(augmentedGrammar,slritems);
    printf("\n");


    printf("First Set\n");
    printf("-----------------\n");
    calculateFistSet(augmentedGrammar,firstSetMap);
    for(const auto& temp1:firstSetMap)
    {
        std::cout<<temp1.first<<":{ ";
        for(const auto& temp2:temp1.second)
        {
            std::cout<<temp2<<", ";
        }
        std::cout<<" }"<<std::endl;
    }

    printf("Follow Set\n");
    printf("-----------------\n");
    calculateFollowSet(augmentedGrammar,firstSetMap,followSetMap);
    for(const auto& temp1:followSetMap)
    {
        std::cout<<temp1.first<<":{ ";
        for(const auto& temp2:temp1.second)
        {
            std::cout<<temp2<<", ";
        }
        std::cout<<" }"<<std::endl;
    }

    printf("Sets of LR(0) Items\n");
    printf("-------------------\n");
    while(++itemid<slritems.size())
    {
        get_SLR_items(slritems,augmentedGrammar,itemid,GOTO);
    }
    printf("\n");


    return 0;
}