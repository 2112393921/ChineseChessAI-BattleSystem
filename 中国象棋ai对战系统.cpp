#define _CRT_SECURE_NO_WARNINGS
#undef UNICODE
#undef _UNICODE
#include <iostream>
#include <vector>
#include <algorithm>
#include <chrono>
#include <limits>
#include <tuple>
#include <cstdlib>
#include <easyx.h>
#include <conio.h>
#include <windows.h>
#include <math.h>
#include <omp.h>
#include <string>
#include <thread>

using namespace std;

// -------------------- 棋盘常量 --------------------
const int ROWS = 10;
const int COLS = 9;
const int EMPTY = 0;

enum PieceType { KING = 1, ADVISOR = 2, ELEPHANT = 3, ROOK = 4, KNIGHT = 5, CANNON = 6, PAWN = 7 };
enum PlayerColor { PLAYER_RED = 1, PLAYER_BLACK = -1 };

// ============================================================
// AI 强度设置（修改此处即可调整棋力）
// ============================================================
const int BUILTIN_DEPTH = 5;          // 内置AI搜索深度（后备）
const int ENGINE_DEPTH = 10;           // 皮卡鱼引擎搜索深度（推荐10~16）
const int ENGINE_THREADS = 8;         // 引擎线程数（根据CPU核心数）
const int ENGINE_HASH_SIZE = 512;     // 引擎哈希表大小（MB）
// ============================================================

using Board = vector<vector<int>>;

// 棋子名称（中文）
const char* PIECE_NAMES[][2] = {
    {"", ""}, {"帅", "将"}, {"仕", "士"}, {"相", "象"},
    {"车", "车"}, {"马", "马"}, {"炮", "炮"}, {"兵", "卒"}
};

int g_lastFromR = -1, g_lastFromC = -1;
int g_lastToR = -1, g_lastToC = -1;
bool g_hasLastMove = false;
int g_selectedRow = -1, g_selectedCol = -1;
vector<tuple<int, int, int, int>> g_validMoves;

// ========== 悔棋历史记录 ==========
struct HistoryEntry {
    int fromR, fromC, toR, toC;
    int captured;
    int turn;
};
vector<HistoryEntry> history;

// -------------------- 基础函数 --------------------
int colorOf(int val) {
    return (val > 0) ? PLAYER_RED : (val < 0 ? PLAYER_BLACK : 0);
}
bool inBoard(int r, int c) { return r >= 0 && r < ROWS && c >= 0 && c < COLS; }
bool inRedPalace(int r, int c) { return r >= 7 && r <= 9 && c >= 3 && c <= 5; }
bool inBlackPalace(int r, int c) { return r >= 0 && r <= 2 && c >= 3 && c <= 5; }
bool inRedSide(int r) { return r >= 5; }
bool inBlackSide(int r) { return r <= 4; }

pair<int, int> findKing(const Board& b, int color) {
    int target = color * KING;
    for (int r = 0; r < ROWS; ++r)
        for (int c = 0; c < COLS; ++c)
            if (b[r][c] == target) return { r,c };
    return { -1,-1 };
}
bool kingsFacing(const Board& b, int color) {
    auto [kr, kc] = findKing(b, color);
    auto [er, ec] = findKing(b, -color);
    if (kr == -1 || er == -1) return false;
    if (kc != ec) return false;
    int r1 = min(kr, er), r2 = max(kr, er);
    for (int r = r1 + 1; r < r2; ++r)
        if (b[r][kc] != EMPTY) return false;
    return true;
}

// -------------------- 走法生成 --------------------
vector<pair<int, int>> genKingMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int dr[] = { -1,1,0,0 }, dc[] = { 0,0,-1,1 };
    auto palace = (color == PLAYER_RED) ? inRedPalace : inBlackPalace;
    for (int i = 0; i < 4; ++i) {
        int nr = r + dr[i], nc = c + dc[i];
        if (inBoard(nr, nc) && palace(nr, nc)) res.push_back({ nr,nc });
    }
    return res;
}
vector<pair<int, int>> genAdvisorMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int dr[] = { -1,-1,1,1 }, dc[] = { -1,1,-1,1 };
    auto palace = (color == PLAYER_RED) ? inRedPalace : inBlackPalace;
    for (int i = 0; i < 4; ++i) {
        int nr = r + dr[i], nc = c + dc[i];
        if (inBoard(nr, nc) && palace(nr, nc)) res.push_back({ nr,nc });
    }
    return res;
}
vector<pair<int, int>> genElephantMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int dr[] = { -2,-2,2,2 }, dc[] = { -2,2,-2,2 };
    auto side = (color == PLAYER_RED) ? inRedSide : inBlackSide;
    for (int i = 0; i < 4; ++i) {
        int nr = r + dr[i], nc = c + dc[i];
        int br = r + dr[i] / 2, bc = c + dc[i] / 2;
        if (inBoard(nr, nc) && side(nr) && b[br][bc] == EMPTY)
            res.push_back({ nr,nc });
    }
    return res;
}
vector<pair<int, int>> genRookMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int dr[] = { -1,1,0,0 }, dc[] = { 0,0,-1,1 };
    for (int i = 0; i < 4; ++i) {
        int nr = r + dr[i], nc = c + dc[i];
        while (inBoard(nr, nc)) {
            if (b[nr][nc] == EMPTY) res.push_back({ nr,nc });
            else { if (colorOf(b[nr][nc]) != color) res.push_back({ nr,nc }); break; }
            nr += dr[i]; nc += dc[i];
        }
    }
    return res;
}
vector<pair<int, int>> genKnightMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int jumps[8][4] = {
        {-2,-1,-1,0},{-2,1,-1,0},{2,-1,1,0},{2,1,1,0},{-1,-2,0,-1},{1,-2,0,-1},{-1,2,0,1},{1,2,0,1}
    };
    for (auto& j : jumps) {
        int nr = r + j[0], nc = c + j[1];
        int br = r + j[2], bc = c + j[3];
        if (inBoard(nr, nc) && b[br][bc] == EMPTY && colorOf(b[nr][nc]) != color) res.push_back({ nr,nc });
    }
    return res;
}
vector<pair<int, int>> genCannonMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int dr[] = { -1,1,0,0 }, dc[] = { 0,0,-1,1 };
    for (int i = 0; i < 4; ++i) {
        int nr = r + dr[i], nc = c + dc[i];
        bool jumped = false;
        while (inBoard(nr, nc)) {
            if (!jumped) { if (b[nr][nc] == EMPTY) res.push_back({ nr,nc }); else jumped = true; }
            else { if (b[nr][nc] != EMPTY) { if (colorOf(b[nr][nc]) != color) res.push_back({ nr,nc }); break; } }
            nr += dr[i]; nc += dc[i];
        }
    }
    return res;
}
vector<pair<int, int>> genPawnMoves(const Board& b, int r, int c, int color) {
    vector<pair<int, int>> res;
    int forward = (color == PLAYER_RED) ? -1 : 1;
    bool crossed = (color == PLAYER_RED) ? (r <= 4) : (r >= 5);
    int nr = r + forward;
    if (inBoard(nr, c) && colorOf(b[nr][c]) != color) res.push_back({ nr,c });
    if (crossed) { for (int dc : {-1, 1}) { int nc = c + dc; if (inBoard(r, nc) && colorOf(b[r][nc]) != color) res.push_back({ r,nc }); } }
    return res;
}

bool isAttackedBy(const Board& b, int row, int col, int color) {
    for (int r = 0; r < ROWS; ++r) {
        for (int c = 0; c < COLS; ++c) {
            int val = b[r][c];
            if (colorOf(val) != color) continue;
            int type = abs(val);
            vector<pair<int, int>> targets;
            switch (type) {
            case KING: targets = genKingMoves(b, r, c, color); break;
            case ADVISOR: targets = genAdvisorMoves(b, r, c, color); break;
            case ELEPHANT: targets = genElephantMoves(b, r, c, color); break;
            case ROOK: targets = genRookMoves(b, r, c, color); break;
            case KNIGHT: targets = genKnightMoves(b, r, c, color); break;
            case CANNON: targets = genCannonMoves(b, r, c, color); break;
            case PAWN: targets = genPawnMoves(b, r, c, color); break;
            }
            for (auto& t : targets) {
                if (t.first == row && t.second == col) return true;
            }
        }
    }
    return false;
}

using Move = tuple<int, int, int, int>;

vector<Move> generateMoves(const Board& b, int color) {
    vector<Move> moves;
    for (int r = 0; r < ROWS; ++r) for (int c = 0; c < COLS; ++c) {
        int val = b[r][c];
        if (colorOf(val) != color) continue;
        int type = abs(val);
        vector<pair<int, int>> targets;
        switch (type) {
        case KING: targets = genKingMoves(b, r, c, color); break;
        case ADVISOR: targets = genAdvisorMoves(b, r, c, color); break;
        case ELEPHANT: targets = genElephantMoves(b, r, c, color); break;
        case ROOK: targets = genRookMoves(b, r, c, color); break;
        case KNIGHT: targets = genKnightMoves(b, r, c, color); break;
        case CANNON: targets = genCannonMoves(b, r, c, color); break;
        case PAWN: targets = genPawnMoves(b, r, c, color); break;
        }
        for (auto [tr, tc] : targets) {
            if (colorOf(b[tr][tc]) == color) continue;
            Board sim = b;
            sim[tr][tc] = sim[r][c];
            sim[r][c] = EMPTY;
            if (kingsFacing(sim, color)) continue;
            pair<int, int> kingPos = findKing(sim, color);
            if (kingPos.first == -1) continue;
            if (isAttackedBy(sim, kingPos.first, kingPos.second, -color)) continue;
            moves.push_back({ r,c,tr,tc });
        }
    }
    return moves;
}

// -------------------- 内置评估（后备） --------------------
const int BASE_VALUES[] = { 0, 10000, 200, 200, 900, 400, 450, 100 };

const int POS_PAWN[ROWS][COLS] = {
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {90,90,110,120,120,120,110,90,90},{95,100,115,125,135,125,115,100,95},
    {95,105,115,125,135,125,115,105,95},{90,100,110,120,130,120,110,100,90},
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0}
};
const int POS_KNIGHT[ROWS][COLS] = {
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0},{0,0,10,15,20,15,10,0,0},{0,0,10,20,25,20,10,0,0},
    {0,0,10,15,20,15,10,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0}
};
const int POS_CANNON[ROWS][COLS] = {
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0},{0,0,5,10,15,10,5,0,0},{0,0,5,10,20,10,5,0,0},
    {0,0,5,10,15,10,5,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0}
};
const int POS_ROOK[ROWS][COLS] = {
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0},{0,0,0,10,15,10,0,0,0},{0,0,0,15,20,15,0,0,0},
    {0,0,0,10,15,10,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0}
};
const int POS_ADVISOR[ROWS][COLS] = {
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0},{0,0,0,15,0,15,0,0,0},{0,0,0,0,0,0,0,0,0},{0,0,0,15,0,15,0,0,0}
};

int getPosValue(int type, int r, int c, int color) {
    if (color == PLAYER_BLACK) { r = ROWS - 1 - r; c = COLS - 1 - c; }
    switch (type) {
    case PAWN: return POS_PAWN[r][c];
    case KNIGHT: return POS_KNIGHT[r][c];
    case CANNON: return POS_CANNON[r][c];
    case ROOK: return POS_ROOK[r][c];
    case ADVISOR: return POS_ADVISOR[r][c];
    default: return 0;
    }
}

int kingSafety(const Board& b, int color) {
    pair<int, int> king = findKing(b, color);
    if (king.first == -1) return -10000;
    int r = king.first, c = king.second;
    int enemy = -color;
    int attackScore = 0;
    for (int dr = -1; dr <= 1; ++dr) for (int dc = -1; dc <= 1; ++dc) {
        int nr = r + dr, nc = c + dc;
        if (inBoard(nr, nc) && colorOf(b[nr][nc]) == enemy) {
            int type = abs(b[nr][nc]);
            attackScore += BASE_VALUES[type] / 10;
        }
    }
    int defense = 0;
    for (int dr = -1; dr <= 1; ++dr) for (int dc = -1; dc <= 1; ++dc) {
        int nr = r + dr, nc = c + dc;
        if (inBoard(nr, nc) && colorOf(b[nr][nc]) == color) {
            int type = abs(b[nr][nc]);
            if (type == ADVISOR) defense += 15;
        }
    }
    return defense - attackScore * 2;
}

int evaluate(const Board& b) {
    int score = 0;
    int redMobility = 0, blackMobility = 0;
    for (int r = 0; r < ROWS; ++r) for (int c = 0; c < COLS; ++c) {
        int val = b[r][c];
        if (val == EMPTY) continue;
        int color = colorOf(val);
        int type = abs(val);
        int base = BASE_VALUES[type];
        int pos = getPosValue(type, r, c, color);
        int valScore = base + pos;
        score += (color == PLAYER_RED ? 1 : -1) * valScore;
        if (type != KING) {
            if (color == PLAYER_RED) redMobility++;
            else blackMobility++;
        }
    }
    score += (redMobility - blackMobility) * 2;
    score += (kingSafety(b, PLAYER_RED) - kingSafety(b, PLAYER_BLACK));
    return score;
}

// -------------------- Alpha-Beta（后备） --------------------
int alphaBeta(Board& b, int depth, int alpha, int beta, bool maximizing, int color) {
    if (depth == 0) return evaluate(b);
    auto moves = generateMoves(b, color);
    if (moves.empty()) return maximizing ? -99999 + (3 - depth) : 99999 - (3 - depth);
    sort(moves.begin(), moves.end(), [&](const Move& a, const Move& bb) {
        int va = abs(b[get<2>(bb)][get<3>(bb)]);
        int vb = abs(b[get<2>(a)][get<3>(a)]);
        return va > vb;
        });
    if (maximizing) {
        for (auto [fr, fc, tr, tc] : moves) {
            Board sim = b;
            sim[tr][tc] = sim[fr][fc];
            sim[fr][fc] = EMPTY;
            int val = alphaBeta(sim, depth - 1, alpha, beta, false, -color);
            alpha = max(alpha, val);
            if (beta <= alpha) break;
        }
        return alpha;
    }
    else {
        for (auto [fr, fc, tr, tc] : moves) {
            Board sim = b;
            sim[tr][tc] = sim[fr][fc];
            sim[fr][fc] = EMPTY;
            int val = alphaBeta(sim, depth - 1, alpha, beta, true, -color);
            beta = min(beta, val);
            if (beta <= alpha) break;
        }
        return beta;
    }
}

Move findBestMove(const Board& b, int color, int depth) {
    auto moves = generateMoves(b, color);
    if (moves.empty()) return { -1,-1,-1,-1 };
    if (moves.size() == 1) return moves[0];
    vector<int> scores(moves.size(), 0);
#pragma omp parallel for
    for (int i = 0; i < (int)moves.size(); ++i) {
        auto [fr, fc, tr, tc] = moves[i];
        Board sim = b;
        sim[tr][tc] = sim[fr][fc];
        sim[fr][fc] = EMPTY;
        bool maximizing = (-color == PLAYER_RED);
        scores[i] = alphaBeta(sim, depth - 1, -1e9, 1e9, maximizing, -color);
    }
    int bestIdx = 0;
    if (color == PLAYER_RED) {
        int bestScore = -1e9;
        for (int i = 0; i < (int)scores.size(); ++i) if (scores[i] > bestScore) { bestScore = scores[i]; bestIdx = i; }
    }
    else {
        int bestScore = 1e9;
        for (int i = 0; i < (int)scores.size(); ++i) if (scores[i] < bestScore) { bestScore = scores[i]; bestIdx = i; }
    }
    return moves[bestIdx];
}

Board initBoard() {
    Board b(ROWS, vector<int>(COLS, EMPTY));
    int back[] = { ROOK, KNIGHT, ELEPHANT, ADVISOR, KING, ADVISOR, ELEPHANT, KNIGHT, ROOK };
    for (int c = 0; c < 9; ++c) { b[0][c] = PLAYER_BLACK * back[c]; b[9][c] = PLAYER_RED * back[c]; }
    b[2][1] = PLAYER_BLACK * CANNON; b[2][7] = PLAYER_BLACK * CANNON;
    b[7][1] = PLAYER_RED * CANNON; b[7][7] = PLAYER_RED * CANNON;
    for (int c = 0; c < 9; c += 2) { b[3][c] = PLAYER_BLACK * PAWN; b[6][c] = PLAYER_RED * PAWN; }
    return b;
}

// -------------------- 图形界面 --------------------
const int CELL_SIZE = 60;
const int BOARD_LEFT = 30;
const int BOARD_TOP = 30;

void drawBoard(const Board& b) {
    BeginBatchDraw();
    setbkcolor(0xF5DEB3);
    cleardevice();

    setlinecolor(0x4A3520);
    setlinestyle(PS_SOLID, 2);
    for (int r = 0; r < ROWS; ++r) {
        int y = BOARD_TOP + r * CELL_SIZE;
        line(BOARD_LEFT, y, BOARD_LEFT + (COLS - 1) * CELL_SIZE, y);
    }
    for (int c = 0; c < COLS; ++c) {
        int x = BOARD_LEFT + c * CELL_SIZE;
        if (c == 0 || c == 8) line(x, BOARD_TOP, x, BOARD_TOP + (ROWS - 1) * CELL_SIZE);
        else {
            line(x, BOARD_TOP, x, BOARD_TOP + 4 * CELL_SIZE);
            line(x, BOARD_TOP + 5 * CELL_SIZE, x, BOARD_TOP + 9 * CELL_SIZE);
        }
    }
    line(BOARD_LEFT + 3 * CELL_SIZE, BOARD_TOP, BOARD_LEFT + 5 * CELL_SIZE, BOARD_TOP + 2 * CELL_SIZE);
    line(BOARD_LEFT + 5 * CELL_SIZE, BOARD_TOP, BOARD_LEFT + 3 * CELL_SIZE, BOARD_TOP + 2 * CELL_SIZE);
    line(BOARD_LEFT + 3 * CELL_SIZE, BOARD_TOP + 7 * CELL_SIZE, BOARD_LEFT + 5 * CELL_SIZE, BOARD_TOP + 9 * CELL_SIZE);
    line(BOARD_LEFT + 5 * CELL_SIZE, BOARD_TOP + 7 * CELL_SIZE, BOARD_LEFT + 3 * CELL_SIZE, BOARD_TOP + 9 * CELL_SIZE);

    // 棋盘线画完后，绘制棋子——注意这里做了视觉翻转
    for (int r = 0; r < ROWS; ++r) {
        for (int c = 0; c < COLS; ++c) {
            int val = b[r][c];
            if (val == EMPTY) continue;

            // 核心翻转：显示时上下颠倒，数据不变
            int displayR = ROWS - 1 - r;
            int displayC = c;

            int x = BOARD_LEFT + displayC * CELL_SIZE;
            int y = BOARD_TOP + displayR * CELL_SIZE;
            bool isRed = (val > 0);
            setfillcolor(isRed ? 0xCC4422 : 0x334455);
            setlinecolor(isRed ? 0x661100 : 0x223344);
            fillcircle(x, y, 26);
            setlinecolor(isRed ? 0xAA4422 : 0x445566);
            circle(x, y, 22);
            int type = abs(val);
            const char* name = PIECE_NAMES[type][isRed ? 0 : 1];
            settextcolor(isRed ? 0xFFEEDD : 0xDDEEFF);
            settextstyle(24, 0, "宋体");
            setbkmode(TRANSPARENT);
            outtextxy(x - 12, y - 12, name);
        }
    }

    settextcolor(0x8B6B3C);
    settextstyle(20, 0, "宋体");
    outtextxy(BOARD_LEFT + 3 * CELL_SIZE, BOARD_TOP + 4.5 * CELL_SIZE - 10, "楚 河 汉 界");

    // ---- 最后一步走法箭头（视觉翻转） ----
    if (g_hasLastMove && g_lastFromR != -1) {
        int displayFromR = ROWS - 1 - g_lastFromR;
        int displayFromC = g_lastFromC;
        int displayToR = ROWS - 1 - g_lastToR;
        int displayToC = g_lastToC;

        int x1 = BOARD_LEFT + displayFromC * CELL_SIZE;
        int y1 = BOARD_TOP + displayFromR * CELL_SIZE;
        int x2 = BOARD_LEFT + displayToC * CELL_SIZE;
        int y2 = BOARD_TOP + displayToR * CELL_SIZE;

        setlinecolor(RGB(255, 0, 0));
        setlinestyle(PS_SOLID, 3);
        line(x1, y1, x2, y2);
        double angle = atan2(y2 - y1, x2 - x1);
        int arrowLen = 15;
        int x3 = x2 - (int)(arrowLen * cos(angle - 0.4));
        int y3 = y2 - (int)(arrowLen * sin(angle - 0.4));
        int x4 = x2 - (int)(arrowLen * cos(angle + 0.4));
        int y4 = y2 - (int)(arrowLen * sin(angle + 0.4));
        setlinecolor(RGB(255, 0, 0));
        setlinestyle(PS_SOLID, 3);
        line(x2, y2, x3, y3);
        line(x2, y2, x4, y4);
        setfillcolor(RGB(255, 0, 0));
        fillcircle(x2, y2, 6);
    }

    // ---- 选中高亮和走法提示（视觉翻转） ----
    if (g_selectedRow != -1) {
        int displayR = ROWS - 1 - g_selectedRow;
        int displayC = g_selectedCol;
        int x = BOARD_LEFT + displayC * CELL_SIZE;
        int y = BOARD_TOP + displayR * CELL_SIZE;
        setlinecolor(YELLOW);
        circle(x, y, 30);

        for (auto& m : g_validMoves) {
            int tr = get<2>(m);
            int tc = get<3>(m);
            int displayTr = ROWS - 1 - tr;
            int displayTc = tc;
            int tx = BOARD_LEFT + displayTc * CELL_SIZE;
            int ty = BOARD_TOP + displayTr * CELL_SIZE;
            setfillcolor(0x00CC44);
            fillcircle(tx, ty, 10);
        }
    }

    EndBatchDraw();
}

// ========== 皮卡鱼引擎封装 ==========
class PikafishEngine {
private:
    HANDLE hProcess;
    HANDLE hStdinWrite;
    HANDLE hStdoutRead;
    PROCESS_INFORMATION pi;
    bool initialized;
    bool engineInited;

public:
    PikafishEngine() : hProcess(NULL), hStdinWrite(NULL), hStdoutRead(NULL),
        initialized(false), engineInited(false) {
    }
    ~PikafishEngine() { close(); }

    bool start(const std::string& enginePath) {
        SECURITY_ATTRIBUTES sa = { sizeof(SECURITY_ATTRIBUTES), NULL, TRUE };
        HANDLE hStdinRead, hStdoutWrite;
        if (!CreatePipe(&hStdinRead, &hStdinWrite, &sa, 0)) return false;
        if (!CreatePipe(&hStdoutRead, &hStdoutWrite, &sa, 0)) return false;
        STARTUPINFOA si = { sizeof(STARTUPINFOA) };
        si.dwFlags = STARTF_USESTDHANDLES;
        si.hStdInput = hStdinRead;
        si.hStdOutput = hStdoutWrite;
        si.hStdError = hStdoutWrite;
        std::string cmd = "\"" + enginePath + "\"";
        if (!CreateProcessA(NULL, (LPSTR)cmd.c_str(), NULL, NULL, TRUE,
            CREATE_NO_WINDOW, NULL, NULL, &si, &pi)) {
            CloseHandle(hStdinRead); CloseHandle(hStdoutWrite);
            CloseHandle(hStdinWrite); CloseHandle(hStdoutRead);
            return false;
        }
        CloseHandle(hStdinRead); CloseHandle(hStdoutWrite);
        hProcess = pi.hProcess;
        initialized = true;
        return true;
    }

    void sendCommand(const std::string& cmd) {
        if (!initialized) return;
        std::string data = cmd + "\n";
        DWORD written;
        WriteFile(hStdinWrite, data.c_str(), (DWORD)data.size(), &written, NULL);
    }

    std::string readUntil(const std::string& marker, int timeoutMs = 5000) {
        if (!initialized) return "";
        char buffer[4096];
        std::string output;
        auto start = std::chrono::steady_clock::now();
        while (true) {
            DWORD avail = 0;
            if (PeekNamedPipe(hStdoutRead, NULL, 0, NULL, &avail, NULL) && avail > 0) {
                DWORD read;
                ReadFile(hStdoutRead, buffer, sizeof(buffer) - 1, &read, NULL);
                buffer[read] = '\0';
                output += buffer;
                if (output.find(marker) != std::string::npos) break;
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
            if (std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start).count() > timeoutMs) {
                break;
            }
        }
        return output;
    }

    bool initEngine() {
        if (!initialized) return false;
        if (engineInited) return true;
        sendCommand("uci");
        std::string response = readUntil("uciok", 5000);
        bool ok = response.find("uciok") != std::string::npos;
        if (ok) {
            engineInited = true;
            cout << "引擎 UCI 初始化成功。" << endl;
        }
        else {
            cout << "引擎 UCI 初始化失败。" << endl;
        }
        return ok;
    }

    void setOption(const std::string& name, const std::string& value) {
        sendCommand("setoption name " + name + " value " + value);
    }

    void setPosition(const std::string& fen) {
        sendCommand("position fen " + fen);
    }

    std::string getBestMove(int depth = 10) {
        sendCommand("go depth " + std::to_string(depth));
        std::string result = readUntil("bestmove", 15000);
        size_t pos = result.find("bestmove");
        if (pos != std::string::npos) {
            std::string moveStr = result.substr(pos + 9);
            size_t space = moveStr.find(' ');
            if (space != std::string::npos) moveStr = moveStr.substr(0, space);
            return moveStr;
        }
        if (!result.empty()) cout << "引擎原始响应: " << result << endl;
        return "";
    }

    std::string getBestMoveFromFEN(const std::string& fen, int depth = 10) {
        if (!initialized) { cout << "引擎未初始化。" << endl; return ""; }
        if (!initEngine()) { cout << "引擎初始化失败。" << endl; return ""; }
        setPosition(fen);
        // 等待引擎就绪（增加超时到10秒）
        sendCommand("isready");
        std::string readyResp = readUntil("readyok", 10000);
        if (readyResp.find("readyok") == std::string::npos) {
            cout << "引擎未就绪（超时10秒）。" << endl;
            return "";
        }
        return getBestMove(depth);
    }

    void close() {
        if (hStdinWrite) {
            sendCommand("quit");
            Sleep(100);
            CloseHandle(hStdinWrite); hStdinWrite = NULL;
        }
        if (hStdoutRead) {
            CloseHandle(hStdoutRead); hStdoutRead = NULL;
        }
        if (hProcess) {
            WaitForSingleObject(hProcess, 1000);
            CloseHandle(hProcess); hProcess = NULL;
        }
        if (pi.hThread) CloseHandle(pi.hThread);
        initialized = false;
        engineInited = false;
    }
};

// ========== 辅助函数 ==========
string boardToFEN(const Board& board, int turn) {
    const char* pieceRed[] = { "", "K", "A", "B", "R", "N", "C", "P" };
    const char* pieceBlack[] = { "", "k", "a", "b", "r", "n", "c", "p" };
    string fen;
    for (int r = 0; r < ROWS; ++r) {
        int empty = 0;
        for (int c = 0; c < COLS; ++c) {
            int val = board[r][c];
            if (val == EMPTY) {
                empty++;
            }
            else {
                if (empty > 0) { fen += to_string(empty); empty = 0; }
                int color = colorOf(val);
                int type = abs(val);
                fen += (color == PLAYER_RED) ? pieceRed[type] : pieceBlack[type];
            }
        }
        if (empty > 0) fen += to_string(empty);
        if (r < ROWS - 1) fen += '/';
    }
    fen += (turn == PLAYER_RED) ? " w" : " b";
    fen += " - - 0 1";
    return fen;
}

// ========== 代数坐标转棋盘坐标 ==========
bool algebraicToBoard(const string& move, int& fr, int& fc, int& tr, int& tc) {
    if (move.length() < 4 || move == "(none)" || move == "none" || move.empty()) return false;
    char fc_char = move[0], tc_char = move[2];
    fc = fc_char - 'a';
    tc = tc_char - 'a';
    if (fc < 0 || fc > 8 || tc < 0 || tc > 8) return false;

    // 镜像映射：代数行 1~9 -> 棋盘行 8~0
    fr = 9 - (move[1] - '0');
    tr = 9 - (move[3] - '0');
    if (fr >= 0 && fr <= 9 && tr >= 0 && tr <= 9) {
        return true;
    }
    return false;
}

// -------------------- 主函数 --------------------
int main() {
    // ==========================================================
    // 模式选择菜单
    // ==========================================================
    cout << "========================================\n";
    cout << " 中国象棋 AI - 模式选择\n";
    cout << "========================================\n";
    cout << "引擎搜索深度 = " << ENGINE_DEPTH << "（引擎可用时优先）\n";
    cout << "----------------------------------------\n";
    cout << "1. AI执黑后走\n";
    cout << "2. AI执红先走\n";
    cout << "请输入数字 1 或 2 选择模式：";
    int mode;
    cin >> mode;
    while (mode != 1 && mode != 2) {
        cout << "输入无效，请输入 1 或 2：";
        cin >> mode;
    }
    // 设置先手
    int firstPlayer;
    string modeDesc;
    if (mode == 1) {
        firstPlayer = PLAYER_BLACK;
        modeDesc = "您执红先走，AI执黑后走";
    }
    else {
        firstPlayer = PLAYER_RED;
        modeDesc = "AI执红先走，您执黑后走";
    }
    cout << "模式" << mode << "：" << modeDesc << "\n";
    cout << "========================================\n";

    system("cls");

    // ==========================================================
    // 图形初始化
    // ==========================================================
    initgraph(630, 660, EX_SHOWCONSOLE);
    Board board = initBoard();
    int turn = firstPlayer;
    bool gameOver = false;
    g_selectedRow = -1; g_selectedCol = -1;
    g_validMoves.clear();
    g_hasLastMove = false;
    g_lastFromR = -1; g_lastFromC = -1;
    g_lastToR = -1; g_lastToC = -1;
    history.clear();

    int stepCount = 0;

    chrono::steady_clock::time_point playerStart, aiStart;
    double totalTimeRed = 0.0;
    double totalTimeBlack = 0.0;

    if (mode == 1) {
        cout << "中国象棋 AI (内置深度 " << BUILTIN_DEPTH << ", 您执红先走)\n";
    }
    else {
        cout << "中国象棋 AI (内置深度 " << BUILTIN_DEPTH << ", AI执红先走，您执黑后走)\n";
    }
    cout << "正在加载皮卡鱼引擎..." << endl;

    PikafishEngine engine;
    bool engineLoaded = false;
    string enginePath = "D:\\皮卡鱼 20260131\\pikafish-avx512.exe";
    if (engine.start(enginePath)) {
        if (engine.initEngine()) {
            engine.sendCommand("setoption name Threads value " + to_string(ENGINE_THREADS));
            engine.sendCommand("setoption name Hash value " + to_string(ENGINE_HASH_SIZE));
            cout << "皮卡鱼引擎加载成功！" << endl;
            engineLoaded = true;
        }
        else {
            cout << "引擎初始化失败，使用内置AI。" << endl;
        }
    }
    else {
        cout << "引擎启动失败，使用内置AI。" << endl;
    }

    cout << "点击红色棋子，再点击绿色目标走棋。按 R 键悔棋。\n";

    // ==========================================================
    // AI 先走（模式2）
    // ==========================================================
    if (mode == 2) {
        cout << "AI 先走..." << endl;
        bool moveDone = false;
        if (engineLoaded) {
            engine.sendCommand("isready");
            string readyResp = engine.readUntil("readyok", 10000);
            if (readyResp.find("readyok") != string::npos) {
                string fen = boardToFEN(board, PLAYER_RED);
                string algebraicMove = engine.getBestMoveFromFEN(fen, ENGINE_DEPTH);
                if (!algebraicMove.empty()) {
                    int fr, fc, tr, tc;
                    if (algebraicToBoard(algebraicMove, fr, fc, tr, tc)) {
                        HistoryEntry aiEntry;
                        aiEntry.fromR = fr; aiEntry.fromC = fc;
                        aiEntry.toR = tr; aiEntry.toC = tc;
                        aiEntry.captured = board[tr][tc];
                        aiEntry.turn = PLAYER_RED;
                        history.push_back(aiEntry);
                        if (history.size() > 100) history.erase(history.begin());

                        board[tr][tc] = board[fr][fc];
                        board[fr][fc] = EMPTY;
                        g_lastFromR = fr; g_lastFromC = fc;
                        g_lastToR = tr; g_lastToC = tc;
                        g_hasLastMove = true;
                        moveDone = true;
                        cout << "AI 先走(引擎): " << fr << " " << fc << " " << tr << " " << tc << endl;
                        stepCount++;
                    }
                }
            }
            else {
                cout << "引擎未就绪，使用内置AI先走。" << endl;
            }
        }
        if (!moveDone) {
            Move aiMove = findBestMove(board, PLAYER_RED, BUILTIN_DEPTH);
            if (get<0>(aiMove) != -1) {
                int fr = get<0>(aiMove), fc = get<1>(aiMove);
                int tr = get<2>(aiMove), tc = get<3>(aiMove);
                HistoryEntry aiEntry;
                aiEntry.fromR = fr; aiEntry.fromC = fc;
                aiEntry.toR = tr; aiEntry.toC = tc;
                aiEntry.captured = board[tr][tc];
                aiEntry.turn = PLAYER_RED;
                history.push_back(aiEntry);
                if (history.size() > 100) history.erase(history.begin());

                board[tr][tc] = board[fr][fc];
                board[fr][fc] = EMPTY;
                g_lastFromR = fr; g_lastFromC = fc;
                g_lastToR = tr; g_lastToC = tc;
                g_hasLastMove = true;
                cout << "AI 先走(内置): " << fr << " " << fc << " " << tr << " " << tc << endl;
                stepCount++;
            }
        }
        turn = PLAYER_BLACK;
        drawBoard(board);
    }

    // ==========================================================
    // 主循环
    // ==========================================================
    try {
        while (!gameOver) {
            // 悔棋
            if (GetAsyncKeyState('R') & 0x8000) {
                if (history.size() >= 2) {
                    HistoryEntry last = history.back();
                    history.pop_back();
                    board[last.fromR][last.fromC] = board[last.toR][last.toC];
                    board[last.toR][last.toC] = last.captured;

                    last = history.back();
                    history.pop_back();
                    board[last.fromR][last.fromC] = board[last.toR][last.toC];
                    board[last.toR][last.toC] = last.captured;

                    turn = PLAYER_BLACK;

                    g_hasLastMove = false;
                    g_lastFromR = -1; g_lastFromC = -1;
                    g_lastToR = -1; g_lastToC = -1;
                    g_selectedRow = -1; g_selectedCol = -1;
                    g_validMoves.clear();
                    drawBoard(board);
                    cout << "已悔棋一步" << endl;
                    Sleep(200);
                }
                else {
                    cout << "没有更多步数可以悔棋" << endl;
                    Sleep(200);
                }
            }

            drawBoard(board);
            ExMessage msg;
            while (peekmessage(&msg, EX_MOUSE)) {
                if (msg.message == WM_LBUTTONDOWN) {
                    // ----- 鼠标点击：视觉坐标 → 数据坐标 -----
                    int visualCol = (msg.x - BOARD_LEFT + CELL_SIZE / 2) / CELL_SIZE;
                    int visualRow = (msg.y - BOARD_TOP + CELL_SIZE / 2) / CELL_SIZE;
                    int dataR = ROWS - 1 - visualRow;
                    int dataC = visualCol;

                    if (inBoard(dataR, dataC) && turn == PLAYER_BLACK) {
                        int val = board[dataR][dataC];
                        auto it = find_if(g_validMoves.begin(), g_validMoves.end(),
                            [&](const Move& m) { return get<2>(m) == dataR && get<3>(m) == dataC; });

                        if (it != g_validMoves.end()) {
                            auto playerEnd = chrono::steady_clock::now();
                            double playerStep = chrono::duration<double>(playerEnd - playerStart).count();
                            totalTimeBlack += playerStep;
                            int fr = get<0>(*it), fc = get<1>(*it);

                            HistoryEntry entry;
                            entry.fromR = fr;
                            entry.fromC = fc;
                            entry.toR = dataR;
                            entry.toC = dataC;
                            entry.captured = board[dataR][dataC];
                            entry.turn = PLAYER_BLACK;
                            history.push_back(entry);
                            if (history.size() > 100) history.erase(history.begin());

                            cout << "你走: " << fr << " " << fc << " " << dataR << " " << dataC << " 耗时 " << playerStep << " 秒\n";

                            board[dataR][dataC] = board[fr][fc];
                            board[fr][fc] = EMPTY;
                            g_selectedRow = -1; g_selectedCol = -1;
                            g_validMoves.clear();
                            g_hasLastMove = false;
                            g_lastFromR = -1; g_lastFromC = -1;
                            g_lastToR = -1; g_lastToC = -1;
                            turn = PLAYER_RED;
                            drawBoard(board);

                            if (findKing(board, PLAYER_BLACK).first == -1) {
                                gameOver = true;
                                MessageBoxA(GetHWnd(), "红方胜利！", "游戏结束", MB_OK);
                                break;
                            }
                            if (generateMoves(board, PLAYER_RED).empty()) {
                                gameOver = true;
                                MessageBoxA(GetHWnd(), "黑方胜利！", "游戏结束", MB_OK);
                                break;
                            }
                            aiStart = chrono::steady_clock::now();
                            stepCount++;

                            // ---------- AI 走棋 ----------
                            bool moveDone = false;
                            if (engineLoaded) {
                                if (stepCount % 10 == 0) {
                                    engine.sendCommand("setoption name Clear Hash");
                                    cout << "已清理引擎哈希表。" << endl;
                                }

                                string fen = boardToFEN(board, PLAYER_RED);
                                string algebraicMove = engine.getBestMoveFromFEN(fen, ENGINE_DEPTH);
                                if (!algebraicMove.empty()) {
                                    int fr2, fc2, tr2, tc2;
                                    if (algebraicToBoard(algebraicMove, fr2, fc2, tr2, tc2)) {
                                        HistoryEntry aiEntry;
                                        aiEntry.fromR = fr2;
                                        aiEntry.fromC = fc2;
                                        aiEntry.toR = tr2;
                                        aiEntry.toC = tc2;
                                        aiEntry.captured = board[tr2][tc2];
                                        aiEntry.turn = PLAYER_RED;
                                        history.push_back(aiEntry);
                                        if (history.size() > 100) history.erase(history.begin());

                                        board[tr2][tc2] = board[fr2][fc2];
                                        board[fr2][fc2] = EMPTY;
                                        g_lastFromR = fr2; g_lastFromC = fc2;
                                        g_lastToR = tr2; g_lastToC = tc2;
                                        g_hasLastMove = true;
                                        moveDone = true;
                                        auto aiEnd = chrono::steady_clock::now();
                                        double aiStep = chrono::duration<double>(aiEnd - aiStart).count();
                                        totalTimeRed += aiStep;
                                        cout << "AI(引擎): " << fr2 << " " << fc2 << " " << tr2 << " " << tc2 << " 耗时 " << aiStep << " 秒\n";
                                    }
                                }
                            }
                            if (!moveDone) {
                                Move aiMove = findBestMove(board, PLAYER_RED, BUILTIN_DEPTH);
                                auto aiEnd = chrono::steady_clock::now();
                                double aiStep = chrono::duration<double>(aiEnd - aiStart).count();
                                totalTimeRed += aiStep;
                                if (get<0>(aiMove) != -1) {
                                    int fr2 = get<0>(aiMove), fc2 = get<1>(aiMove);
                                    int tr2 = get<2>(aiMove), tc2 = get<3>(aiMove);
                                    HistoryEntry aiEntry;
                                    aiEntry.fromR = fr2;
                                    aiEntry.fromC = fc2;
                                    aiEntry.toR = tr2;
                                    aiEntry.toC = tc2;
                                    aiEntry.captured = board[tr2][tc2];
                                    aiEntry.turn = PLAYER_RED;
                                    history.push_back(aiEntry);
                                    if (history.size() > 100) history.erase(history.begin());

                                    board[tr2][tc2] = board[fr2][fc2];
                                    board[fr2][fc2] = EMPTY;
                                    g_lastFromR = fr2; g_lastFromC = fc2;
                                    g_lastToR = tr2; g_lastToC = tc2;
                                    g_hasLastMove = true;
                                    cout << "AI(内置): " << fr2 << " " << fc2 << " " << tr2 << " " << tc2 << " 耗时 " << aiStep << " 秒\n";
                                }
                            }

                            turn = PLAYER_BLACK;
                            drawBoard(board);
                            Sleep(50);

                            if (findKing(board, PLAYER_RED).first == -1) {
                                gameOver = true;
                                MessageBoxA(GetHWnd(), "黑方胜利！", "游戏结束", MB_OK);
                                break;
                            }
                            if (generateMoves(board, PLAYER_BLACK).empty()) {
                                gameOver = true;
                                MessageBoxA(GetHWnd(), "红方胜利！", "游戏结束", MB_OK);
                                break;
                            }
                            continue;
                        }

                        // 选中己方棋子（玩家执黑）
                        if (colorOf(val) == PLAYER_BLACK) {
                            g_selectedRow = dataR;
                            g_selectedCol = dataC;
                            g_validMoves.clear();
                            auto allMoves = generateMoves(board, PLAYER_BLACK);
                            for (auto& m : allMoves) {
                                if (get<0>(m) == dataR && get<1>(m) == dataC)
                                    g_validMoves.push_back(m);
                            }
                            playerStart = chrono::steady_clock::now();
                        }
                        else {
                            g_selectedRow = -1;
                            g_selectedCol = -1;
                            g_validMoves.clear();
                        }
                    }
                }
            }
            Sleep(20);
        }
    }
    catch (...) {
        engine.close();
        cout << "发生异常，引擎已关闭。" << endl;
        throw;
    }

    engine.close();

    char buf[256];
    sprintf_s(buf, "红方总耗时: %.2f 秒\n黑方总耗时: %.2f 秒", totalTimeRed, totalTimeBlack);
    MessageBoxA(GetHWnd(), buf, "双方总耗时统计", MB_OK);

    closegraph();
    return 0;
}
