// Compile with c++ ece650-a2cpp -std=c++11 -o ece650-a2
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <memory>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
#include <algorithm>
#include <iostream>
#include <iterator>
#include <queue>
#include <regex>
#include <sstream>
#include <string>

using namespace std;

// reset all values in the graph
void reset(vector<vector<bool>> &matrix)
{

  int vertices = (int)matrix.size();
  // Initialize adjacency matrix
  for (int r = 0; r < vertices; r++)
  {
    for (int c = 0; c < vertices; c++)
    {
      matrix[r][c] = false;
    }
  }
}

// construct the edges in the graph matrix according to the specified input
void build_graph(string inputEdges, vector<vector<bool>> &matrix, vector<tuple<int, int>> &edgesList)
{
  int size = (int)matrix.size();
  // 'r' in the string 'inputEdges'. 'm' is flag for determining matching behavior.
  regex r("<.*?>");
  smatch m;
  bool invalidVertex = false;
  for (sregex_iterator iterator =
           sregex_iterator(inputEdges.begin(), inputEdges.end(), r);
       iterator != sregex_iterator(); iterator++)
  {
    smatch match;
    match = *iterator;
    string edges;
    edges = match.str(0);
    for (int i = 0; i < match.length(); i++)
    {
      // traverse every edge to extract vertices
      string edge = match[i];
      int edge_array[2] = {-1, -1};
      int vertex_index = 0;
      if (edge.length() > 0)
      {
        string edge_vertices = edge.substr(1, edge.length() - 2);
        char *edges_pointer = &edge_vertices[0];

        char *token = strtok(edges_pointer, ",");

        while (token != NULL)
        {
          edge_array[vertex_index] = stoi(token);
          vertex_index++;
          token = strtok(NULL, ",");
        }
         //Create an  adjacency matrix as per given edge 
        if ((edge_array[0] > 0 && edge_array[1] > 0) &&
            (edge_array[0] <= size && edge_array[1] <= size &&
             (edge_array[0] != edge_array[1])))
        {
          matrix[edge_array[0]-1][edge_array[1]-1] = true;
          edgesList.push_back(make_tuple(edge_array[0]-1, edge_array[1]-1));
          matrix[edge_array[1]-1][edge_array[0]-1] = true;
        }
        else
        {
          invalidVertex = true;
          break;
        }
      }
    }
  }
  if (invalidVertex)
  {
    cout << "Error: Invalid Edge specified" << endl;
    // Remove all the edges in case of invalid input edges
    reset(matrix);
  }
};

// initialise the graph matrix with the number of vertices
void initialiseGraph(int vertices, vector<vector<bool>> &matrix)
{
  int numV = (int)matrix.size();
  // Resize the matrix to size vertex * vertex
  for (int i = 0; i < numV; i++)
    matrix[i].resize(vertices);
  matrix.resize(vertices, vector<bool>(vertices));

  // Set all values in the matrix to false
  for (int r = 0; r < vertices; r++)
  {
    for (int c = 0; c < vertices; c++)
    {
      matrix[r][c] = false;
    }
  }
};


vector<int> vertexCover(vector<vector<bool>> &matrix, vector<tuple<int, int>> &edgesList, int kVal)
{
  //cout << "hello" <<endl;
  //cout << kVal << endl;
  vector<int> vertex_cover;
  int num_vertices = (int)matrix.size();
  // As we need to reset it I used heap 
  std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
  std::vector<std::vector<Minisat::Lit>> x(num_vertices);
  for (int i = 0; i < num_vertices; i++)
  {
    for (int j = 0; j < kVal; j++)
    {
      Minisat::Lit literal = Minisat::mkLit(solver->newVar());
      x[i].push_back(literal);
    }
  }

  // Clause 1: At least one vertex is the ith vertex in the vertex cover:
  for (int j = 0; j < kVal; j++)
  {
    Minisat::vec<Minisat::Lit> col_entries;
    for (int i = 0; i < num_vertices; i++)
    {
      col_entries.push(x[i][j]);
    }
    solver->addClause(col_entries);
    col_entries.clear();
  };

  // // Clause 2:  No one vertex can appear twice in a vertex cover
  for (int i = 0; i < (kVal - 1); i++)
  {
    for (int j = i + 1; j < kVal; j++)
    {
      for (int l = 0; l < num_vertices; l++)
      {
        solver->addClause(~x[l][i], ~x[l][j]);
      }
    }
  }

  // Clause 3: No more than one vertex appears in the mth position of the vertex cover
  for (int i = 0; i < (num_vertices - 1); i++)
  {
    for (int j = i + 1; j < num_vertices; j++)
    {
      for (int k = 0; k < kVal; k++)
      {
        solver->addClause(~x[i][k], ~x[j][k]);
      }
    }
  }

  //Clause 4: Every edge is incident to at least one vertex in the vertex cover.
  for (int edge_index = 0; edge_index < (int)edgesList.size(); edge_index++)
  {
    Minisat::vec<Minisat::Lit> edge_entries;
    for (int k = 0; k < kVal; k++)
    {
      int v1 = get<0>(edgesList[edge_index]);
      int v2 = get<1>(edgesList[edge_index]);
      edge_entries.push(x[v1][k]);
      edge_entries.push(x[v2][k]);
    }
    solver->addClause(edge_entries);
    edge_entries.clear();
  }
  bool res = solver->solve();
  if (res)
  {
    // cout << "KValue: "<< kVal << endl; 
    // cout << solver->nClauses()<< endl;
    for (int i = 0; i < num_vertices; i++)
    {
      for (int j = 0; j < kVal; j++)
      {
        Minisat::lbool is_val_vertex_cover = solver->modelValue(x[i][j]);
        if (is_val_vertex_cover == Minisat::l_True)
        {
          vertex_cover.push_back(i);
        }
      }
    }
    reset(matrix);
    return vertex_cover;
  }
  else {
    return {-99};
  }
  return vertex_cover;
}

int main(int argc, char **argv)
{
 static int vertices = 10;
  vector<tuple<int, int>> edgesList;

  while (!cin.eof())
  {
    string inputLine;
    getline(std::cin, inputLine);

    vector<string> inputArgs;
    istringstream inputStream(inputLine);
    string value = "";
    while (inputStream >> value)
    {
      inputArgs.push_back(value);
    }
    char command = inputArgs.at(0)[0];
    // initialize adjacency matrix as 10*10, would be overriden by V command
    static vector<vector<bool>> matrix(vertices, vector<bool>(vertices));
    string edges = "";

    switch (command)
    {
    case 'E':
    {
      if (inputArgs.size() != 2)
      {
        cout << "Error: Invalid arguments for E command" << endl;
      }
      else
      {
        edges = inputArgs.at(1);
        edgesList.clear();
        build_graph(edges, matrix, edgesList);
        if(edgesList.size() == 0){
          cout << endl;
          continue;
        }
        int low = 0;
        int high = vertices;
        
        vector<int> new_vertex_cover;
        vector<int> result;
        vector<int> temp = {-99};
        while (low <= high)
        {
          int mid = ((low + high) / 2);
          result = vertexCover(matrix, edgesList, mid);
          if(result != temp)
          {
            high = mid - 1;
            new_vertex_cover.clear();
            new_vertex_cover = result;
          }
          else
          {
            low = mid + 1;
          }
        }

        sort(new_vertex_cover.begin(), new_vertex_cover.end());

        for (int index =0; index < (int)new_vertex_cover.size(); index++){
          cout << new_vertex_cover[index] + 1;
          if(index!=(int)new_vertex_cover.size()-1){
            cout << " ";
          }
        }
        cout << endl;
      break;
    }
    case 'V':
    {
      if (inputArgs.size() != 2)
      {
        cout << "Error: Invalid arguments for V command" << endl;
      }
      else
      {
        vertices = stoi(inputArgs.at(1));
        initialiseGraph(vertices, matrix);
      }
      break;
    }
    default:
      cout << "Error: Command not supported" << endl;
      break;
    }
  };
  }
  return 0;
}

// V 5
// E {<1,5>,<5,2>,<1,4>,<4,5>,<4,3>,<2,4>}