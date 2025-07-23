#include <iostream>
#include <sstream>
#include <vector>
#include <array>
#include <cstdint>
#include <cstdio>
#include <algorithm>
#include <random>
#include <chrono>
#include <cstring>
#include <bit>

// Type definitions
using u64 = uint64_t;
using u32 = uint32_t;
using u16 = uint16_t;
using u8 = uint8_t;

// Constants
constexpr int MAX_PLY = 128;
constexpr int MAX_MOVES = 256;
constexpr int MATE_SCORE = 32000;
constexpr int INF = 32001;
constexpr int TT_SIZE = 1 << 20; // 1M entries

// Square indices (0-63)
enum Square {
    A1, B1, C1, D1, E1, F1, G1, H1,
    A2, B2, C2, D2, E2, F2, G2, H2,
    A3, B3, C3, D3, E3, F3, G3, H3,
    A4, B4, C4, D4, E4, F4, G4, H4,
    A5, B5, C5, D5, E5, F5, G5, H5,
    A6, B6, C6, D6, E6, F6, G6, H6,
    A7, B7, C7, D7, E7, F7, G7, H7,
    A8, B8, C8, D8, E8, F8, G8, H8,
    NO_SQUARE = 64
};

// Piece types
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, NO_PIECE_TYPE };

// Colors
enum Color { WHITE, BLACK, NO_COLOR };

// Castling rights
enum CastlingRight { 
    WHITE_OO = 1, WHITE_OOO = 2, BLACK_OO = 4, BLACK_OOO = 8,
    NO_CASTLING = 0, ANY_CASTLING = 15
};

// Move structure
struct Move {
    u16 data;
    
    Move() : data(0) {}
    Move(int from, int to, int flags = 0) : data(from | (to << 6) | (flags << 12)) {}
    
    int from() const { return data & 0x3F; }
    int to() const { return (data >> 6) & 0x3F; }
    int flags() const { return (data >> 12) & 0xF; }
    
    bool operator==(const Move& m) const { return data == m.data; }
    bool operator!=(const Move& m) const { return data != m.data; }
};

// Move flags
enum MoveFlags {
    NORMAL = 0,
    PROMOTION_N = 1, PROMOTION_B = 2, PROMOTION_R = 3, PROMOTION_Q = 4,
    EP_CAPTURE = 5, DOUBLE_PUSH = 6, KING_CASTLE = 7, QUEEN_CASTLE = 8
};

// Transposition table entry
struct TTEntry {
    u64 key;
    int score;
    int depth;
    u8 flag;
    Move move;
};

// Bitboard utilities
constexpr u64 bit(int sq) { return 1ULL << sq; }
constexpr u64 rank_bb(int r) { return 0xFFULL << (r * 8); }
constexpr u64 file_bb(int f) { return 0x0101010101010101ULL << f; }

constexpr u64 RANK_1 = rank_bb(0);
constexpr u64 RANK_2 = rank_bb(1);
constexpr u64 RANK_3 = rank_bb(2);
constexpr u64 RANK_4 = rank_bb(3);
constexpr u64 RANK_5 = rank_bb(4);
constexpr u64 RANK_6 = rank_bb(5);
constexpr u64 RANK_7 = rank_bb(6);
constexpr u64 RANK_8 = rank_bb(7);

constexpr u64 FILE_A = file_bb(0);
constexpr u64 FILE_B = file_bb(1);
constexpr u64 FILE_H = file_bb(7);

constexpr u64 NOT_FILE_A = ~FILE_A;
constexpr u64 NOT_FILE_H = ~FILE_H;

// Zobrist keys
u64 zobrist_pieces[2][6][64];
u64 zobrist_side;
u64 zobrist_castling[16];
u64 zobrist_ep[8];

// Attack tables
u64 knight_attacks[64];
u64 king_attacks[64];
u64 pawn_attacks[2][64];

// Magic bitboards for sliding pieces
struct Magic {
    u64* attacks;
    u64 mask;
    u64 magic;
    int shift;
};

Magic bishop_magics[64];
Magic rook_magics[64];

// Precomputed tables
int piece_values[6] = { 100, 300, 300, 500, 900, 20000 };

// Piece-square tables [piece_type][square]
int pst[6][64] = {
    // Pawn
    {
         0,  0,  0,  0,  0,  0,  0,  0,
         5, 10, 10,-20,-20, 10, 10,  5,
         5, -5,-10,  0,  0,-10, -5,  5,
         0,  0,  0, 20, 20,  0,  0,  0,
         5,  5, 10, 25, 25, 10,  5,  5,
        10, 10, 20, 30, 30, 20, 10, 10,
        50, 50, 50, 50, 50, 50, 50, 50,
         0,  0,  0,  0,  0,  0,  0,  0
    },
    // Knight
    {
        -50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20,  0,  5,  5,  0,-20,-40,
        -30,  5, 10, 15, 15, 10,  5,-30,
        -30,  0, 15, 20, 20, 15,  0,-30,
        -30,  5, 15, 20, 20, 15,  5,-30,
        -30,  0, 10, 15, 15, 10,  0,-30,
        -40,-20,  0,  0,  0,  0,-20,-40,
        -50,-40,-30,-30,-30,-30,-40,-50
    },
    // Bishop
    {
        -20,-10,-10,-10,-10,-10,-10,-20,
        -10,  5,  0,  0,  0,  0,  5,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10,  0, 10, 10, 10, 10,  0,-10,
        -10,  5,  5, 10, 10,  5,  5,-10,
        -10,  0,  5, 10, 10,  5,  0,-10,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -20,-10,-10,-10,-10,-10,-10,-20
    },
    // Rook
    {
         0,  0,  0,  5,  5,  0,  0,  0,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
         5, 10, 10, 10, 10, 10, 10,  5,
         0,  0,  0,  0,  0,  0,  0,  0
    },
    // Queen
    {
        -20,-10,-10, -5, -5,-10,-10,-20,
        -10,  0,  5,  0,  0,  0,  0,-10,
        -10,  5,  5,  5,  5,  5,  0,-10,
          0,  0,  5,  5,  5,  5,  0, -5,
         -5,  0,  5,  5,  5,  5,  0, -5,
        -10,  0,  5,  5,  5,  5,  0,-10,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -20,-10,-10, -5, -5,-10,-10,-20
    },
    // King
    {
         20, 30, 10,  0,  0, 10, 30, 20,
         20, 20,  0,  0,  0,  0, 20, 20,
        -10,-20,-20,-20,-20,-20,-20,-10,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30
    }
};

// King endgame PST
int king_endgame_pst[64] = {
    -50,-30,-30,-30,-30,-30,-30,-50,
    -30,-30,  0,  0,  0,  0,-30,-30,
    -30,-10, 20, 30, 30, 20,-10,-30,
    -30,-10, 30, 40, 40, 30,-10,-30,
    -30,-10, 30, 40, 40, 30,-10,-30,
    -30,-10, 20, 30, 30, 20,-10,-30,
    -30,-20,-10,  0,  0,-10,-20,-30,
    -50,-40,-30,-20,-20,-30,-40,-50
};

// Board class
class Board {
public:
    u64 pieces[2][6];  // [color][piece_type]
    u64 occupied[2];   // [color]
    u64 all_pieces;
    
    int side_to_move;
    int castling_rights;
    int ep_square;
    int halfmove_clock;
    int fullmove_number;
    
    u64 hash_key;
    
    // History for undoing moves
    struct UndoInfo {
        int castling_rights;
        int ep_square;
        int halfmove_clock;
        u64 hash_key;
        int captured_piece;
    };
    
    std::vector<UndoInfo> history;
    
    Board() { set_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"); }
    
    void set_fen(const std::string& fen);
    std::string get_fen() const;
    
    void make_move(Move move);
    void undo_move(Move move);
    
    bool is_square_attacked(int sq, int by_side) const;
    // IMPORTANT: in_check() checks if the CURRENT side to move is in check
    // After making a move, this checks the NEW side, not the side that just moved!
    bool in_check() const { return is_square_attacked(king_square(side_to_move), side_to_move ^ 1); }
    
    int piece_on(int sq) const;
    int king_square(int color) const { return __builtin_ctzll(pieces[color][KING]); }
    
    void update_hash_key();
    u64 get_hash() const { return hash_key; }
    
    // Move generation
    void generate_moves(Move* moves, int& count) const;
    void generate_captures(Move* moves, int& count) const;
    
private:
    void add_move(Move* moves, int& count, int from, int to, int flags = 0) const;
    void generate_pawn_moves(Move* moves, int& count, bool captures_only) const;
    void generate_piece_moves(Move* moves, int& count, int piece_type, bool captures_only) const;
    void generate_castling_moves(Move* moves, int& count) const;
};

// Initialize attack tables
void init_attacks() {
    // Knight attacks
    int knight_offsets[] = { -17, -15, -10, -6, 6, 10, 15, 17 };
    for (int sq = 0; sq < 64; sq++) {
        u64 attacks = 0;
        for (int i = 0; i < 8; i++) {
            int to = sq + knight_offsets[i];
            if (to >= 0 && to < 64) {
                int from_file = sq & 7;
                int to_file = to & 7;
                if (abs(from_file - to_file) <= 2) {
                    attacks |= bit(to);
                }
            }
        }
        knight_attacks[sq] = attacks;
    }
    
    // King attacks
    int king_offsets[] = { -9, -8, -7, -1, 1, 7, 8, 9 };
    for (int sq = 0; sq < 64; sq++) {
        u64 attacks = 0;
        for (int i = 0; i < 8; i++) {
            int to = sq + king_offsets[i];
            if (to >= 0 && to < 64) {
                int from_file = sq & 7;
                int to_file = to & 7;
                if (abs(from_file - to_file) <= 1) {
                    attacks |= bit(to);
                }
            }
        }
        king_attacks[sq] = attacks;
    }
    
    // Pawn attacks
    for (int sq = 0; sq < 64; sq++) {
        // White pawns
        u64 attacks = 0;
        if (sq % 8 != 0 && sq < 56) attacks |= bit(sq + 7);
        if (sq % 8 != 7 && sq < 56) attacks |= bit(sq + 9);
        pawn_attacks[WHITE][sq] = attacks;
        
        // Black pawns
        attacks = 0;
        if (sq % 8 != 0 && sq > 7) attacks |= bit(sq - 9);
        if (sq % 8 != 7 && sq > 7) attacks |= bit(sq - 7);
        pawn_attacks[BLACK][sq] = attacks;
    }
}

// Simple sliding piece attacks (no magic bitboards for brevity)
u64 get_bishop_attacks(int sq, u64 occupied) {
    u64 attacks = 0;
    int directions[] = { -9, -7, 7, 9 };
    
    for (int dir : directions) {
        int from = sq;
        while (true) {
            from += dir;
            if (from < 0 || from >= 64) break;
            if (abs((from % 8) - ((from - dir) % 8)) != 1) break;
            
            attacks |= bit(from);
            if (occupied & bit(from)) break;
        }
    }
    return attacks;
}

u64 get_rook_attacks(int sq, u64 occupied) {
    u64 attacks = 0;
    int directions[] = { -8, -1, 1, 8 };
    
    for (int dir : directions) {
        int from = sq;
        while (true) {
            from += dir;
            if (from < 0 || from >= 64) break;
            if (dir == 1 && from % 8 == 0) break;
            if (dir == -1 && from % 8 == 7) break;
            
            attacks |= bit(from);
            if (occupied & bit(from)) break;
        }
    }
    return attacks;
}

u64 get_queen_attacks(int sq, u64 occupied) {
    return get_bishop_attacks(sq, occupied) | get_rook_attacks(sq, occupied);
}

// Initialize Zobrist keys
void init_zobrist() {
    std::mt19937_64 rng(1234567890);
    
    for (int c = 0; c < 2; c++) {
        for (int p = 0; p < 6; p++) {
            for (int sq = 0; sq < 64; sq++) {
                zobrist_pieces[c][p][sq] = rng();
            }
        }
    }
    
    zobrist_side = rng();
    
    for (int i = 0; i < 16; i++) {
        zobrist_castling[i] = rng();
    }
    
    for (int i = 0; i < 8; i++) {
        zobrist_ep[i] = rng();
    }
}

void Board::set_fen(const std::string& fen) {
    // Clear board
    std::memset(pieces, 0, sizeof(pieces));
    occupied[WHITE] = occupied[BLACK] = all_pieces = 0;
    
    std::istringstream ss(fen);
    std::string board_str, side_str, castle_str, ep_str;
    ss >> board_str >> side_str >> castle_str >> ep_str >> halfmove_clock >> fullmove_number;
    
    // Parse pieces
    int sq = 56;  // Start from a8
    for (char c : board_str) {
        if (c == '/') {
            sq -= 16;
        } else if (c >= '1' && c <= '8') {
            sq += c - '0';
        } else {
            int color = std::isupper(c) ? WHITE : BLACK;
            c = std::tolower(c);
            
            int piece_type = NO_PIECE_TYPE;
            switch (c) {
                case 'p': piece_type = PAWN; break;
                case 'n': piece_type = KNIGHT; break;
                case 'b': piece_type = BISHOP; break;
                case 'r': piece_type = ROOK; break;
                case 'q': piece_type = QUEEN; break;
                case 'k': piece_type = KING; break;
            }
            
            if (piece_type != NO_PIECE_TYPE) {
                pieces[color][piece_type] |= bit(sq);
                occupied[color] |= bit(sq);
                all_pieces |= bit(sq);
            }
            sq++;
        }
    }
    
    // Side to move
    side_to_move = (side_str == "w") ? WHITE : BLACK;
    
    // Castling rights
    castling_rights = 0;
    for (char c : castle_str) {
        switch (c) {
            case 'K': castling_rights |= WHITE_OO; break;
            case 'Q': castling_rights |= WHITE_OOO; break;
            case 'k': castling_rights |= BLACK_OO; break;
            case 'q': castling_rights |= BLACK_OOO; break;
        }
    }
    
    // En passant
    ep_square = NO_SQUARE;
    if (ep_str != "-") {
        int file = ep_str[0] - 'a';
        int rank = ep_str[1] - '1';
        ep_square = rank * 8 + file;
    }
    
    update_hash_key();
}

void Board::update_hash_key() {
    hash_key = 0;
    
    for (int c = 0; c < 2; c++) {
        for (int p = 0; p < 6; p++) {
            u64 bb = pieces[c][p];
            while (bb) {
                int sq = __builtin_ctzll(bb);
                hash_key ^= zobrist_pieces[c][p][sq];
                bb &= bb - 1;
            }
        }
    }
    
    if (side_to_move == BLACK) hash_key ^= zobrist_side;
    hash_key ^= zobrist_castling[castling_rights];
    if (ep_square != NO_SQUARE) hash_key ^= zobrist_ep[ep_square & 7];
}

int Board::piece_on(int sq) const {
    u64 bb = bit(sq);
    if (!(all_pieces & bb)) return NO_PIECE_TYPE;
    
    for (int p = 0; p < 6; p++) {
        if (pieces[WHITE][p] & bb) return p;
        if (pieces[BLACK][p] & bb) return p;
    }
    return NO_PIECE_TYPE;
}

bool Board::is_square_attacked(int sq, int by_side) const {
    u64 sq_bb = bit(sq);
    
    // Pawn attacks
    if (pawn_attacks[by_side ^ 1][sq] & pieces[by_side][PAWN]) return true;
    
    // Knight attacks
    if (knight_attacks[sq] & pieces[by_side][KNIGHT]) return true;
    
    // King attacks
    if (king_attacks[sq] & pieces[by_side][KING]) return true;
    
    // Bishop/Queen attacks
    u64 bishop_attackers = pieces[by_side][BISHOP] | pieces[by_side][QUEEN];
    if (get_bishop_attacks(sq, all_pieces) & bishop_attackers) return true;
    
    // Rook/Queen attacks
    u64 rook_attackers = pieces[by_side][ROOK] | pieces[by_side][QUEEN];
    if (get_rook_attacks(sq, all_pieces) & rook_attackers) return true;
    
    return false;
}

void Board::add_move(Move* moves, int& count, int from, int to, int flags) const {
    moves[count++] = Move(from, to, flags);
}

void Board::generate_pawn_moves(Move* moves, int& count, bool captures_only) const {
    u64 pawns = pieces[side_to_move][PAWN];
    int enemy = side_to_move ^ 1;
    
    while (pawns) {
        int from = __builtin_ctzll(pawns);
        pawns &= pawns - 1;
        
        if (side_to_move == WHITE) {
            // Captures
            u64 attacks = pawn_attacks[WHITE][from] & occupied[BLACK];
            while (attacks) {
                int to = __builtin_ctzll(attacks);
                attacks &= attacks - 1;
                
                if (to >= 56) {  // Promotion
                    add_move(moves, count, from, to, PROMOTION_Q);
                    add_move(moves, count, from, to, PROMOTION_R);
                    add_move(moves, count, from, to, PROMOTION_B);
                    add_move(moves, count, from, to, PROMOTION_N);
                } else {
                    add_move(moves, count, from, to);
                }
            }
            
            // En passant
            if (ep_square != NO_SQUARE && pawn_attacks[WHITE][from] & bit(ep_square)) {
                add_move(moves, count, from, ep_square, EP_CAPTURE);
            }
            
            if (!captures_only) {
                // Single push
                int to = from + 8;
                if (to < 64 && !(all_pieces & bit(to))) {
                    if (to >= 56) {  // Promotion
                        add_move(moves, count, from, to, PROMOTION_Q);
                        add_move(moves, count, from, to, PROMOTION_R);
                        add_move(moves, count, from, to, PROMOTION_B);
                        add_move(moves, count, from, to, PROMOTION_N);
                    } else {
                        add_move(moves, count, from, to);
                    }
                    
                    // Double push
                    if (from >= 8 && from < 16) {
                        to = from + 16;
                        if (!(all_pieces & bit(to))) {
                            add_move(moves, count, from, to, DOUBLE_PUSH);
                        }
                    }
                }
            }
        } else {  // BLACK
            // Captures
            u64 attacks = pawn_attacks[BLACK][from] & occupied[WHITE];
            while (attacks) {
                int to = __builtin_ctzll(attacks);
                attacks &= attacks - 1;
                
                if (to < 8) {  // Promotion
                    add_move(moves, count, from, to, PROMOTION_Q);
                    add_move(moves, count, from, to, PROMOTION_R);
                    add_move(moves, count, from, to, PROMOTION_B);
                    add_move(moves, count, from, to, PROMOTION_N);
                } else {
                    add_move(moves, count, from, to);
                }
            }
            
            // En passant
            if (ep_square != NO_SQUARE && pawn_attacks[BLACK][from] & bit(ep_square)) {
                add_move(moves, count, from, ep_square, EP_CAPTURE);
            }
            
            if (!captures_only) {
                // Single push
                int to = from - 8;
                if (to >= 0 && !(all_pieces & bit(to))) {
                    if (to < 8) {  // Promotion
                        add_move(moves, count, from, to, PROMOTION_Q);
                        add_move(moves, count, from, to, PROMOTION_R);
                        add_move(moves, count, from, to, PROMOTION_B);
                        add_move(moves, count, from, to, PROMOTION_N);
                    } else {
                        add_move(moves, count, from, to);
                    }
                    
                    // Double push
                    if (from >= 48 && from < 56) {
                        to = from - 16;
                        if (!(all_pieces & bit(to))) {
                            add_move(moves, count, from, to, DOUBLE_PUSH);
                        }
                    }
                }
            }
        }
    }
}

void Board::generate_piece_moves(Move* moves, int& count, int piece_type, bool captures_only) const {
    u64 pieces_bb = pieces[side_to_move][piece_type];
    u64 targets = captures_only ? occupied[side_to_move ^ 1] : ~occupied[side_to_move];
    
    while (pieces_bb) {
        int from = __builtin_ctzll(pieces_bb);
        pieces_bb &= pieces_bb - 1;
        
        u64 attacks = 0;
        switch (piece_type) {
            case KNIGHT: attacks = knight_attacks[from]; break;
            case BISHOP: attacks = get_bishop_attacks(from, all_pieces); break;
            case ROOK: attacks = get_rook_attacks(from, all_pieces); break;
            case QUEEN: attacks = get_queen_attacks(from, all_pieces); break;
            case KING: attacks = king_attacks[from]; break;
        }
        
        attacks &= targets;
        while (attacks) {
            int to = __builtin_ctzll(attacks);
            attacks &= attacks - 1;
            add_move(moves, count, from, to);
        }
    }
}

void Board::generate_castling_moves(Move* moves, int& count) const {
    if (side_to_move == WHITE) {
        if ((castling_rights & WHITE_OO) && 
            !(all_pieces & (bit(F1) | bit(G1))) &&
            !is_square_attacked(E1, BLACK) &&
            !is_square_attacked(F1, BLACK) &&
            !is_square_attacked(G1, BLACK)) {
            add_move(moves, count, E1, G1, KING_CASTLE);
        }
        
        if ((castling_rights & WHITE_OOO) &&
            !(all_pieces & (bit(B1) | bit(C1) | bit(D1))) &&
            !is_square_attacked(E1, BLACK) &&
            !is_square_attacked(D1, BLACK) &&
            !is_square_attacked(C1, BLACK)) {
            add_move(moves, count, E1, C1, QUEEN_CASTLE);
        }
    } else {
        if ((castling_rights & BLACK_OO) &&
            !(all_pieces & (bit(F8) | bit(G8))) &&
            !is_square_attacked(E8, WHITE) &&
            !is_square_attacked(F8, WHITE) &&
            !is_square_attacked(G8, WHITE)) {
            add_move(moves, count, E8, G8, KING_CASTLE);
        }
        
        if ((castling_rights & BLACK_OOO) &&
            !(all_pieces & (bit(B8) | bit(C8) | bit(D8))) &&
            !is_square_attacked(E8, WHITE) &&
            !is_square_attacked(D8, WHITE) &&
            !is_square_attacked(C8, WHITE)) {
            add_move(moves, count, E8, C8, QUEEN_CASTLE);
        }
    }
}

void Board::generate_moves(Move* moves, int& count) const {
    count = 0;
    generate_pawn_moves(moves, count, false);
    generate_piece_moves(moves, count, KNIGHT, false);
    generate_piece_moves(moves, count, BISHOP, false);
    generate_piece_moves(moves, count, ROOK, false);
    generate_piece_moves(moves, count, QUEEN, false);
    generate_piece_moves(moves, count, KING, false);
    generate_castling_moves(moves, count);
}

void Board::generate_captures(Move* moves, int& count) const {
    count = 0;
    generate_pawn_moves(moves, count, true);
    generate_piece_moves(moves, count, KNIGHT, true);
    generate_piece_moves(moves, count, BISHOP, true);
    generate_piece_moves(moves, count, ROOK, true);
    generate_piece_moves(moves, count, QUEEN, true);
    generate_piece_moves(moves, count, KING, true);
}

void Board::make_move(Move move) {
    // Save undo info
    UndoInfo undo;
    undo.castling_rights = castling_rights;
    undo.ep_square = ep_square;
    undo.halfmove_clock = halfmove_clock;
    undo.hash_key = hash_key;
    undo.captured_piece = NO_PIECE_TYPE;
    
    int from = move.from();
    int to = move.to();
    int flags = move.flags();
    
    // Find moving piece
    int moving_piece = NO_PIECE_TYPE;
    for (int p = 0; p < 6; p++) {
        if (pieces[side_to_move][p] & bit(from)) {
            moving_piece = p;
            break;
        }
    }
    
    // Handle capture
    if (all_pieces & bit(to)) {
        for (int p = 0; p < 6; p++) {
            if (pieces[side_to_move ^ 1][p] & bit(to)) {
                undo.captured_piece = p;
                pieces[side_to_move ^ 1][p] ^= bit(to);
                occupied[side_to_move ^ 1] ^= bit(to);
                hash_key ^= zobrist_pieces[side_to_move ^ 1][p][to];
                break;
            }
        }
    }
    
    // En passant capture
    if (flags == EP_CAPTURE) {
        int cap_sq = to + (side_to_move == WHITE ? -8 : 8);
        pieces[side_to_move ^ 1][PAWN] ^= bit(cap_sq);
        occupied[side_to_move ^ 1] ^= bit(cap_sq);
        all_pieces ^= bit(cap_sq);
        hash_key ^= zobrist_pieces[side_to_move ^ 1][PAWN][cap_sq];
        undo.captured_piece = PAWN;
    }
    
    // Move piece
    pieces[side_to_move][moving_piece] ^= bit(from) | bit(to);
    occupied[side_to_move] ^= bit(from) | bit(to);
    all_pieces = occupied[WHITE] | occupied[BLACK];
    
    hash_key ^= zobrist_pieces[side_to_move][moving_piece][from];
    hash_key ^= zobrist_pieces[side_to_move][moving_piece][to];
    
    // Handle special moves
    if (flags == DOUBLE_PUSH) {
        ep_square = to + (side_to_move == WHITE ? -8 : 8);
        hash_key ^= zobrist_ep[ep_square & 7];
    } else {
        if (ep_square != NO_SQUARE) {
            hash_key ^= zobrist_ep[ep_square & 7];
        }
        ep_square = NO_SQUARE;
    }
    
    // Promotions
    if (flags >= PROMOTION_N && flags <= PROMOTION_Q) {
        int promo_piece = flags - PROMOTION_N + KNIGHT;
        pieces[side_to_move][PAWN] ^= bit(to);
        pieces[side_to_move][promo_piece] ^= bit(to);
        hash_key ^= zobrist_pieces[side_to_move][PAWN][to];
        hash_key ^= zobrist_pieces[side_to_move][promo_piece][to];
    }
    
    // Castling
    if (flags == KING_CASTLE) {
        if (side_to_move == WHITE) {
            pieces[WHITE][ROOK] ^= bit(H1) | bit(F1);
            occupied[WHITE] ^= bit(H1) | bit(F1);
            hash_key ^= zobrist_pieces[WHITE][ROOK][H1];
            hash_key ^= zobrist_pieces[WHITE][ROOK][F1];
        } else {
            pieces[BLACK][ROOK] ^= bit(H8) | bit(F8);
            occupied[BLACK] ^= bit(H8) | bit(F8);
            hash_key ^= zobrist_pieces[BLACK][ROOK][H8];
            hash_key ^= zobrist_pieces[BLACK][ROOK][F8];
        }
        all_pieces = occupied[WHITE] | occupied[BLACK];
    } else if (flags == QUEEN_CASTLE) {
        if (side_to_move == WHITE) {
            pieces[WHITE][ROOK] ^= bit(A1) | bit(D1);
            occupied[WHITE] ^= bit(A1) | bit(D1);
            hash_key ^= zobrist_pieces[WHITE][ROOK][A1];
            hash_key ^= zobrist_pieces[WHITE][ROOK][D1];
        } else {
            pieces[BLACK][ROOK] ^= bit(A8) | bit(D8);
            occupied[BLACK] ^= bit(A8) | bit(D8);
            hash_key ^= zobrist_pieces[BLACK][ROOK][A8];
            hash_key ^= zobrist_pieces[BLACK][ROOK][D8];
        }
        all_pieces = occupied[WHITE] | occupied[BLACK];
    }
    
    // Update castling rights
    hash_key ^= zobrist_castling[castling_rights];
    
    if (moving_piece == KING) {
        castling_rights &= side_to_move == WHITE ? ~(WHITE_OO | WHITE_OOO) : ~(BLACK_OO | BLACK_OOO);
    }
    
    if (from == A1 || to == A1) castling_rights &= ~WHITE_OOO;
    if (from == H1 || to == H1) castling_rights &= ~WHITE_OO;
    if (from == A8 || to == A8) castling_rights &= ~BLACK_OOO;
    if (from == H8 || to == H8) castling_rights &= ~BLACK_OO;
    
    hash_key ^= zobrist_castling[castling_rights];
    
    // Update counters
    if (moving_piece == PAWN || undo.captured_piece != NO_PIECE_TYPE) {
        halfmove_clock = 0;
    } else {
        halfmove_clock++;
    }
    
    if (side_to_move == BLACK) {
        fullmove_number++;
    }
    
    // Switch side
    side_to_move ^= 1;
    hash_key ^= zobrist_side;
    
    history.push_back(undo);
}

void Board::undo_move(Move move) {
    UndoInfo undo = history.back();
    history.pop_back();
    
    // Switch side back
    side_to_move ^= 1;
    
    int from = move.from();
    int to = move.to();
    int flags = move.flags();
    
    // Find moving piece
    int moving_piece = NO_PIECE_TYPE;
    for (int p = 0; p < 6; p++) {
        if (pieces[side_to_move][p] & bit(to)) {
            moving_piece = p;
            break;
        }
    }
    
    // Handle promotions
    if (flags >= PROMOTION_N && flags <= PROMOTION_Q) {
        int promo_piece = flags - PROMOTION_N + KNIGHT;
        pieces[side_to_move][promo_piece] ^= bit(to);
        pieces[side_to_move][PAWN] ^= bit(to);
        moving_piece = PAWN;
    }
    
    // Move piece back
    pieces[side_to_move][moving_piece] ^= bit(from) | bit(to);
    occupied[side_to_move] ^= bit(from) | bit(to);
    
    // Restore capture
    if (undo.captured_piece != NO_PIECE_TYPE) {
        if (flags == EP_CAPTURE) {
            int cap_sq = to + (side_to_move == WHITE ? -8 : 8);
            pieces[side_to_move ^ 1][PAWN] ^= bit(cap_sq);
            occupied[side_to_move ^ 1] ^= bit(cap_sq);
        } else {
            pieces[side_to_move ^ 1][undo.captured_piece] ^= bit(to);
            occupied[side_to_move ^ 1] ^= bit(to);
        }
    }
    
    // Handle castling
    if (flags == KING_CASTLE) {
        if (side_to_move == WHITE) {
            pieces[WHITE][ROOK] ^= bit(H1) | bit(F1);
            occupied[WHITE] ^= bit(H1) | bit(F1);
        } else {
            pieces[BLACK][ROOK] ^= bit(H8) | bit(F8);
            occupied[BLACK] ^= bit(H8) | bit(F8);
        }
    } else if (flags == QUEEN_CASTLE) {
        if (side_to_move == WHITE) {
            pieces[WHITE][ROOK] ^= bit(A1) | bit(D1);
            occupied[WHITE] ^= bit(A1) | bit(D1);
        } else {
            pieces[BLACK][ROOK] ^= bit(A8) | bit(D8);
            occupied[BLACK] ^= bit(A8) | bit(D8);
        }
    }
    
    all_pieces = occupied[WHITE] | occupied[BLACK];
    
    // Restore state
    castling_rights = undo.castling_rights;
    ep_square = undo.ep_square;
    halfmove_clock = undo.halfmove_clock;
    hash_key = undo.hash_key;
    
    if (side_to_move == BLACK) {
        fullmove_number--;
    }
}

// Transposition table
class TranspositionTable {
    TTEntry* table;
    size_t size;
    
public:
    TranspositionTable() : table(nullptr), size(0) {}
    
    ~TranspositionTable() {
        delete[] table;
    }
    
    void resize(size_t mb) {
        delete[] table;
        size = (mb * 1024 * 1024) / sizeof(TTEntry);
        table = new TTEntry[size]();
    }
    
    void clear() {
        std::memset(table, 0, size * sizeof(TTEntry));
    }
    
    TTEntry* probe(u64 key) {
        return &table[key & (size - 1)];
    }
    
    void store(u64 key, int score, int depth, u8 flag, Move move) {
        TTEntry* entry = probe(key);
        if (entry->depth <= depth || entry->key != key) {
            entry->key = key;
            entry->score = score;
            entry->depth = depth;
            entry->flag = flag;
            entry->move = move;
        }
    }
};

// Search class
class Search {
    Board& board;
    TranspositionTable& tt;
    
    // Search info
    int nodes;
    std::chrono::steady_clock::time_point start_time;
    int time_limit;
    bool stop_search;
    
    // Move ordering
    Move killer_moves[MAX_PLY][2];
    int history_table[2][64][64];
    
    // Principal variation
    Move pv_table[MAX_PLY][MAX_PLY];
    int pv_length[MAX_PLY];
    
public:
    Search(Board& b, TranspositionTable& t) : board(b), tt(t) {}
    
    Move think(int depth_limit, int time_ms);
    
private:
    int alpha_beta(int depth, int alpha, int beta, int ply);
    int quiescence(int alpha, int beta, int ply);
    int evaluate();
    
    void order_moves(Move* moves, int count, Move tt_move, int ply);
    bool is_repetition();
    void update_pv(Move move, int ply);
    void update_killers(Move move, int ply);
    void update_history(Move move, int depth);
    
    bool time_up() {
        if (time_limit == 0) return false;
        if (nodes % 1024 == 0) {  // Check more frequently
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start_time).count();
            return elapsed >= time_limit;
        }
        return false;
    }
};

Move Search::think(int depth_limit, int time_ms) {
    nodes = 0;
    time_limit = time_ms;
    stop_search = false;
    start_time = std::chrono::steady_clock::now();
    
    std::memset(killer_moves, 0, sizeof(killer_moves));
    std::memset(history_table, 0, sizeof(history_table));
    
    // --- START OF FIX ---
    Move moves[MAX_MOVES];
    int move_count;
    board.generate_moves(moves, move_count);
    
    Move best_move; // Will hold the final best move
    Move fallback_move; // A safe fallback
    
    int original_side = board.side_to_move;
    
    // Find the first legal move to use as a fallback
    for (int i = 0; i < move_count; ++i) {
        board.make_move(moves[i]);
        // Correct check: is the side that just moved leaving their king in check?
        if (!board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
            fallback_move = moves[i];
            board.undo_move(moves[i]);
            break;
        }
        board.undo_move(moves[i]);
    }
    
    // If we couldn't find any legal move, it's mate or stalemate.
    // Return immediately with null move
    if (fallback_move.data == 0) {
        return Move(); // UCI::go will handle this as "0000"
    }
    
    best_move = fallback_move; // Initialize best_move with our safe fallback
    // --- END OF FIX ---
    
    int best_score = -INF;
    
    // Iterative deepening
    for (int depth = 1; depth <= depth_limit && !stop_search; depth++) {
        pv_length[0] = 0;
        int score = alpha_beta(depth, -INF, INF, 0);
        
        if (stop_search) break;
        
        // This logic is now safe. If pv_length is 0, we still have our fallback.
        if (pv_length[0] > 0) {
            best_move = pv_table[0][0];
            best_score = score;
            
            // UCI info
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start_time).count();
            
            std::cout << "info depth " << depth;
            std::cout << " score cp " << score;
            std::cout << " nodes " << nodes;
            std::cout << " time " << elapsed;
            std::cout << " pv";
            for (int i = 0; i < pv_length[0]; i++) {
                Move m = pv_table[0][i];
                std::cout << " " << char('a' + (m.from() & 7)) << char('1' + (m.from() >> 3));
                std::cout << char('a' + (m.to() & 7)) << char('1' + (m.to() >> 3));
                if (m.flags() >= PROMOTION_N && m.flags() <= PROMOTION_Q) {
                    const char* pieces = "nbrq";
                    std::cout << pieces[m.flags() - PROMOTION_N];
                }
            }
            std::cout << std::endl;
        }
        
        if (time_up()) {
            stop_search = true;
            break;
        }
    }
    
    return best_move; // This will now always be a valid, legal move.
}

int Search::alpha_beta(int depth, int alpha, int beta, int ply) {
    nodes++;
    if (ply > 0 && (is_repetition() || board.halfmove_clock >= 100)) return 0;
    if (time_up()) {
        stop_search = true;
        return 0;
    }

    pv_length[ply] = ply;
    
    bool is_in_check = board.in_check();
    if (is_in_check) {
        depth++; // Extend search in check
    }

    TTEntry* tt_entry = tt.probe(board.get_hash());
    Move tt_move;
    if (tt_entry->key == board.get_hash() && tt_entry->depth >= depth && ply > 0) {
        int score = tt_entry->score;
        if (score > MATE_SCORE - MAX_PLY) score -= ply;
        else if (score < -MATE_SCORE + MAX_PLY) score += ply;

        if (tt_entry->flag == 0) return score; // Exact
        if (tt_entry->flag == 1 && score >= beta) return beta; // Lower bound
        if (tt_entry->flag == 2 && score <= alpha) return alpha; // Upper bound
        tt_move = tt_entry->move;
    }

    if (depth <= 0) {
        return quiescence(alpha, beta, ply);
    }
    
    // Null move pruning
    if (!is_in_check && depth >= 3 && ply > 0) {
        board.side_to_move ^= 1;
        board.hash_key ^= zobrist_side;
        
        int score = -alpha_beta(depth - 3, -beta, -beta + 1, ply + 1);
        
        board.side_to_move ^= 1;
        board.hash_key ^= zobrist_side;
        
        if (score >= beta) return beta;
    }
    
    // --- START OF NEW, CORRECTED LOGIC ---

    Move moves[MAX_MOVES];
    int move_count;
    board.generate_moves(moves, move_count);
    order_moves(moves, move_count, tt_move, ply);
    
    int legal_moves_found = 0;
    Move best_move;
    u8 tt_flag = 2; // Upper bound (alpha)

    int original_side = board.side_to_move;

    for (int i = 0; i < move_count; i++) {
        board.make_move(moves[i]);

        // Correct legality check, right after making the move
        if (board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
            board.undo_move(moves[i]);
            continue; // Skip illegal moves
        }

        legal_moves_found++;
        int score;

        // Simplified PVS
        if (legal_moves_found == 1) {
            score = -alpha_beta(depth - 1, -beta, -alpha, ply + 1);
        } else {
            // Late Move Reduction (LMR)
            int reduction = 0;
            if (depth >= 3 && legal_moves_found > 4 && moves[i].flags() == NORMAL &&
                !is_in_check && moves[i] != killer_moves[ply][0] && 
                moves[i] != killer_moves[ply][1]) {
                reduction = 1;
            }
            
            score = -alpha_beta(depth - 1 - reduction, -alpha - 1, -alpha, ply + 1);
            
            if (score > alpha && reduction > 0) {
                score = -alpha_beta(depth - 1, -alpha - 1, -alpha, ply + 1); // Re-search
            }
            if (score > alpha && score < beta) {
                score = -alpha_beta(depth - 1, -beta, -alpha, ply + 1); // Full window re-search
            }
        }
        
        board.undo_move(moves[i]);

        if (stop_search) return 0;
        
        if (score > alpha) {
            alpha = score;
            tt_flag = 0; // Exact
            best_move = moves[i];
            update_pv(best_move, ply);

            if (alpha >= beta) {
                tt_flag = 1; // Lower bound (beta)
                if (moves[i].flags() == NORMAL) {
                    update_killers(moves[i], ply);
                    update_history(moves[i], depth);
                }
                break; // Beta cutoff
            }
        }
    }

    if (legal_moves_found == 0) {
        return is_in_check ? (-MATE_SCORE + ply) : 0; // Checkmate or Stalemate
    }
    
    if (!stop_search) {
        tt.store(board.get_hash(), alpha, depth, tt_flag, best_move);
    }

    return alpha;
    // --- END OF NEW LOGIC ---
}

int Search::quiescence(int alpha, int beta, int ply) {
    nodes++;
    
    if (time_up()) {
        stop_search = true;
        return 0;
    }
    
    int stand_pat = evaluate();
    
    if (stand_pat >= beta) return beta;
    if (stand_pat > alpha) alpha = stand_pat;
    
    // Generate captures only
    Move moves[MAX_MOVES];
    int move_count;
    board.generate_captures(moves, move_count);
    
    // Simple MVV-LVA ordering
    std::sort(moves, moves + move_count, [this](const Move& a, const Move& b) {
        int a_victim = board.piece_on(a.to());
        int b_victim = board.piece_on(b.to());
        if (a_victim == NO_PIECE_TYPE) a_victim = 0;
        if (b_victim == NO_PIECE_TYPE) b_victim = 0;
        return piece_values[a_victim] > piece_values[b_victim];
    });
    
    int original_side = board.side_to_move;
    
    for (int i = 0; i < move_count; i++) {
        board.make_move(moves[i]);
        
        // Correct legality check
        if (board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
            board.undo_move(moves[i]);
            continue;
        }
        
        int score = -quiescence(-beta, -alpha, ply + 1);
        board.undo_move(moves[i]);
        
        if (stop_search) return 0;
        
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }
    
    return alpha;
}

int Search::evaluate() {
    int score = 0;
    int phase = 0;  // Game phase (0 = endgame, 24 = opening)
    
    // Material and PST
    for (int p = 0; p < 6; p++) {
        u64 white_pieces = board.pieces[WHITE][p];
        u64 black_pieces = board.pieces[BLACK][p];
        
        while (white_pieces) {
            int sq = __builtin_ctzll(white_pieces);
            white_pieces &= white_pieces - 1;
            
            score += piece_values[p];
            score += pst[p][sq];
            
            if (p != PAWN && p != KING) phase += 1;
        }
        
        while (black_pieces) {
            int sq = __builtin_ctzll(black_pieces);
            black_pieces &= black_pieces - 1;
            
            score -= piece_values[p];
            score -= pst[p][sq ^ 56];  // Flip square for black
            
            if (p != PAWN && p != KING) phase += 1;
        }
    }
    
    // Mobility (simplified)
    Move moves[MAX_MOVES];
    int count;
    
    board.generate_moves(moves, count);
    int our_mobility = count;
    
    board.side_to_move ^= 1;
    board.generate_moves(moves, count);
    int their_mobility = count;
    board.side_to_move ^= 1;
    
    score += (our_mobility - their_mobility) * 2;
    
    // Bishop pair
    if (__builtin_popcountll(board.pieces[WHITE][BISHOP]) >= 2) score += 25;
    if (__builtin_popcountll(board.pieces[BLACK][BISHOP]) >= 2) score -= 25;
    
    // Passed pawns (simplified)
    u64 white_pawns = board.pieces[WHITE][PAWN];
    while (white_pawns) {
        int sq = __builtin_ctzll(white_pawns);
        white_pawns &= white_pawns - 1;
        
        int rank = sq >> 3;
        u64 blockers = 0;
        for (int r = rank + 1; r < 8; r++) {
            blockers |= rank_bb(r);
        }
        
        int file = sq & 7;
        u64 files = file_bb(file);
        if (file > 0) files |= file_bb(file - 1);
        if (file < 7) files |= file_bb(file + 1);
        
        if (!(board.pieces[BLACK][PAWN] & blockers & files)) {
            score += (rank - 1) * 10;  // Passed pawn bonus
        }
    }
    
    u64 black_pawns = board.pieces[BLACK][PAWN];
    while (black_pawns) {
        int sq = __builtin_ctzll(black_pawns);
        black_pawns &= black_pawns - 1;
        
        int rank = sq >> 3;
        u64 blockers = 0;
        for (int r = rank - 1; r >= 0; r--) {
            blockers |= rank_bb(r);
        }
        
        int file = sq & 7;
        u64 files = file_bb(file);
        if (file > 0) files |= file_bb(file - 1);
        if (file < 7) files |= file_bb(file + 1);
        
        if (!(board.pieces[WHITE][PAWN] & blockers & files)) {
            score -= (6 - rank) * 10;  // Passed pawn bonus
        }
    }
    
    // King safety (simplified)
    if (phase > 12) {  // Not endgame
        int white_king_sq = board.king_square(WHITE);
        int black_king_sq = board.king_square(BLACK);
        
        // Pawn shield
        if (white_king_sq < 8) {  // King on back rank
            u64 shield = board.pieces[WHITE][PAWN] & king_attacks[white_king_sq];
            score += __builtin_popcountll(shield) * 10;
        }
        
        if (black_king_sq >= 56) {  // King on back rank
            u64 shield = board.pieces[BLACK][PAWN] & king_attacks[black_king_sq];
            score -= __builtin_popcountll(shield) * 10;
        }
    }
    
    return board.side_to_move == WHITE ? score : -score;
}

void Search::order_moves(Move* moves, int count, Move tt_move, int ply) {
    int scores[MAX_MOVES];
    
    for (int i = 0; i < count; i++) {
        if (moves[i] == tt_move) {
            scores[i] = 1000000;
        } else if (board.all_pieces & bit(moves[i].to())) {
            // MVV-LVA for captures
            int victim = board.piece_on(moves[i].to());
            int attacker = board.piece_on(moves[i].from());
            scores[i] = 10000 + piece_values[victim] - piece_values[attacker];
        } else if (moves[i] == killer_moves[ply][0]) {
            scores[i] = 9000;
        } else if (moves[i] == killer_moves[ply][1]) {
            scores[i] = 8000;
        } else {
            // History heuristic
            scores[i] = history_table[board.side_to_move][moves[i].from()][moves[i].to()];
        }
    }
    
    // Sort by scores
    for (int i = 0; i < count - 1; i++) {
        for (int j = i + 1; j < count; j++) {
            if (scores[j] > scores[i]) {
                std::swap(moves[i], moves[j]);
                std::swap(scores[i], scores[j]);
            }
        }
    }
}

bool Search::is_repetition() {
    if (board.history.size() < 4) return false;
    
    int count = 0;
    for (int i = board.history.size() - 2; i >= 0 && i >= (int)board.history.size() - board.halfmove_clock; i -= 2) {
        if (board.history[i].hash_key == board.hash_key) {
            count++;
            if (count >= 2) return true;
        }
    }
    return false;
}

void Search::update_pv(Move move, int ply) {
    pv_table[ply][ply] = move;
    for (int i = ply + 1; i < pv_length[ply + 1]; i++) {
        pv_table[ply][i] = pv_table[ply + 1][i];
    }
    pv_length[ply] = pv_length[ply + 1];
}

void Search::update_killers(Move move, int ply) {
    if (move != killer_moves[ply][0]) {
        killer_moves[ply][1] = killer_moves[ply][0];
        killer_moves[ply][0] = move;
    }
}

void Search::update_history(Move move, int depth) {
    history_table[board.side_to_move][move.from()][move.to()] += depth * depth;
}

// UCI interface
class UCI {
    Board board;
    TranspositionTable tt;
    
public:
    UCI() {
        tt.resize(16);  // 16 MB default
    }
    
    void loop();
    
private:
    void position(const std::string& line);
    void go(const std::string& line);
    u64 perft(int depth);
    void perft_divide(int depth);
};

void UCI::loop() {
    std::string line;
    
    while (std::getline(std::cin, line)) {
        std::istringstream iss(line);
        std::string command;
        iss >> command;
        
        if (command == "uci") {
            std::cout << "id name ChessEngine" << std::endl;
            std::cout << "id author Assistant" << std::endl;
            std::cout << "option name Hash type spin default 16 min 1 max 1024" << std::endl;
            std::cout << "uciok" << std::endl; // Use endl instead of \n
        }
        else if (command == "isready") {
            std::cout << "readyok" << std::endl; // Use endl instead of \n
        }
        else if (command == "ucinewgame") {
            tt.clear();
        }
        else if (command == "position") {
            position(line);
        }
        else if (command == "go") {
            go(line);
        }
        else if (command == "quit") {
            break;
        }
        else if (command == "perft") {
            int depth;
            iss >> depth;
            auto start = std::chrono::steady_clock::now();
            u64 nodes = perft(depth); // Call the corrected perft
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start).count();
            std::cout << "perft(" << depth << ") = " << nodes 
                      << " | Time: " << elapsed << "ms" << std::endl;
        }
        else if (command == "perftdivide") { // ADD THIS NEW COMMAND HANDLER
            int depth;
            iss >> depth;
            perft_divide(depth);
        }
        else if (command == "setoption") {
            std::string name_token, name, value_token;
            int value;
            iss >> name_token >> name >> value_token >> value;
            if (name == "Hash") {
                tt.resize(value);
            }
        }
    }
}

void UCI::position(const std::string& line) {
    std::istringstream iss(line);
    std::string token;
    iss >> token;  // "position"
    iss >> token;
    
    if (token == "startpos") {
        board.set_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        iss >> token;  // "moves" (optional)
    } else if (token == "fen") {
        std::string fen;
        for (int i = 0; i < 6; i++) {
            iss >> token;
            fen += token + " ";
        }
        board.set_fen(fen);
        iss >> token;  // "moves" (optional)
    }
    
    // Play moves
    if (token == "moves") {
        std::string move_str;
        while (iss >> move_str) {
            // Parse move
            int from = (move_str[0] - 'a') + (move_str[1] - '1') * 8;
            int to = (move_str[2] - 'a') + (move_str[3] - '1') * 8;
            int flags = 0;
            
            if (move_str.length() > 4) {
                switch (move_str[4]) {
                    case 'n': flags = PROMOTION_N; break;
                    case 'b': flags = PROMOTION_B; break;
                    case 'r': flags = PROMOTION_R; break;
                    case 'q': flags = PROMOTION_Q; break;
                }
            }
            
            // Find the matching legal move
            Move moves[MAX_MOVES];
            int count;
            board.generate_moves(moves, count);
            
            int original_side = board.side_to_move;
            Move moveToMake;
            
            for (int i = 0; i < count; i++) {
                if (moves[i].from() == from && moves[i].to() == to) {
                    // For promotions, make sure we have the right promotion piece
                    if (flags != 0) {
                        if (moves[i].flags() == flags) {
                            moveToMake = moves[i];
                            break;
                        }
                    } else {
                        moveToMake = moves[i];
                        // Don't break yet in case there's a promotion move with same from/to
                    }
                }
            }
            
            // Make the move and verify its legality correctly
            if (moveToMake.data != 0) {
                board.make_move(moveToMake);
                // Correct check: If the side that just moved left their king in check, undo
                if (board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
                    board.undo_move(moveToMake);
                    // Move was illegal, but GUI thinks it's legal - this is a problem
                    // For now, we'll just skip it, but this indicates a desync
                }
                // If move was legal, it stays on the board
            }
        }
    }
}

void UCI::go(const std::string& line) {
    std::istringstream iss(line);
    std::string token;
    iss >> token;  // "go"
    
    int depth = 64;
    int time_limit = 0;
    int wtime = 0, btime = 0, winc = 0, binc = 0;
    int movestogo = 40;
    
    while (iss >> token) {
        if (token == "depth") {
            iss >> depth;
        } else if (token == "movetime") {
            iss >> time_limit;
        } else if (token == "wtime") {
            iss >> wtime;
        } else if (token == "btime") {
            iss >> btime;
        } else if (token == "winc") {
            iss >> winc;
        } else if (token == "binc") {
            iss >> binc;
        } else if (token == "movestogo") {
            iss >> movestogo;
        }
    }
    
    // Time management
    if (wtime || btime) {
        int time_left = board.side_to_move == WHITE ? wtime : btime;
        int inc = board.side_to_move == WHITE ? winc : binc;
        
        // More conservative time management to avoid timeouts
        time_limit = (time_left / (movestogo + 5)) + (inc * 0.5);
        time_limit = std::min(time_limit, time_left / 4);  // Never use more than 25% of remaining time
        time_limit = std::max(time_limit, 50);  // Always think for at least 50ms
    }
    
    Search search(board, tt);
    Move best_move = search.think(depth, time_limit);
    
    // Handle null move (checkmate/stalemate)
    if (best_move.data == 0) {
        std::cout << "bestmove 0000" << std::endl;
        return;
    }
    
    std::cout << "bestmove ";
    std::cout << char('a' + (best_move.from() & 7)) << char('1' + (best_move.from() >> 3));
    std::cout << char('a' + (best_move.to() & 7)) << char('1' + (best_move.to() >> 3));
    if (best_move.flags() >= PROMOTION_N && best_move.flags() <= PROMOTION_Q) {
        const char* pieces = "nbrq";
        std::cout << pieces[best_move.flags() - PROMOTION_N];
    }
    std::cout << std::endl;
}

u64 UCI::perft(int depth) {
    if (depth == 0) return 1;
    
    u64 nodes = 0;
    Move moves[MAX_MOVES];
    int count;
    int original_side = board.side_to_move; // Remember whose turn it is
    
    board.generate_moves(moves, count);
    
    for (int i = 0; i < count; i++) {
        board.make_move(moves[i]);
        
        // CORRECT LEGALITY CHECK:
        // Is the king of the side that just moved (original_side) attacked by the new side to move?
        if (!board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
            nodes += perft(depth - 1);
        }
        
        board.undo_move(moves[i]);
    }
    
    return nodes;
}

void UCI::perft_divide(int depth) {
    if (depth == 0) {
        std::cout << "Cannot divide depth 0." << std::endl;
        return;
    }

    std::cout << "Divide for depth " << depth << std::endl;
    u64 total_nodes = 0;
    auto start = std::chrono::steady_clock::now();

    Move moves[MAX_MOVES];
    int count;
    int original_side = board.side_to_move;

    board.generate_moves(moves, count);
    
    // It's helpful to sort moves to get a consistent output for debugging
    std::sort(moves, moves + count, [](const Move& a, const Move& b) {
        if (a.from() != b.from()) return a.from() < b.from();
        return a.to() < b.to();
    });

    for (int i = 0; i < count; i++) {
        Move m = moves[i];
        board.make_move(m);

        if (!board.is_square_attacked(board.king_square(original_side), board.side_to_move)) {
            u64 nodes_for_move = perft(depth - 1);
            total_nodes += nodes_for_move;

            // Print the move and its node count
            std::cout << char('a' + (m.from() & 7)) << char('1' + (m.from() >> 3));
            std::cout << char('a' + (m.to() & 7)) << char('1' + (m.to() >> 3));
            if (m.flags() >= PROMOTION_N && m.flags() <= PROMOTION_Q) {
                const char* pieces = "nbrq";
                std::cout << pieces[m.flags() - PROMOTION_N];
            }
            std::cout << ": " << nodes_for_move << std::endl;
        }
        
        board.undo_move(m);
    }

    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - start).count();

    std::cout << "\nTotal Moves: " << count << std::endl;
    std::cout << "Total Nodes: " << total_nodes << std::endl;
    std::cout << "Time: " << elapsed << "ms" << std::endl;
}

// Main function
int main() {
    // Ensure no buffering on stdout for proper UCI communication
    std::setbuf(stdout, nullptr);
    
    // Initialize tables
    init_attacks();
    init_zobrist();
    
    // Start UCI loop
    UCI uci;
    uci.loop();
    
    return 0;
}